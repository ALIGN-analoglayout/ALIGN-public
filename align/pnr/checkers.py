from ..cell_fabric import transformation, pdk
from .. import primitive
import json
import importlib
import sys
import pathlib
import re

import logging
logger = logging.getLogger(__name__)

def rational_scaling( d, *, mul=1, div=1, errors=None):
    assert all( (mul*c) % div == 0 for c in d['bbox'])
    d['bbox'] = [ (mul*c) //div for c in d['bbox']]
    for term in d['terminals']:
        if not all( (mul*c) % div == 0 for c in term['rect']):
            txt = f"Terminal {term} not a multiple of {div} (mul={mul})."
            if errors is not None:
                errors.append( txt)
            logger.error( txt)

        term['rect'] = [ (mul*c)//div for c in term['rect']]

def gen_viewer_json( hN, *, pdkdir, draw_grid=False, global_route_json=None, json_dir=None, checkOnly=False, extract=False, input_dir=None, markers=False):

    generator = primitive.get_generator('MOSGenerator', pdkdir)
    # TODO: Remove these hardcoded widths & heights from __init__()
    #       (Height may be okay since it defines UnitCellHeight)
    cnv = generator(pdk.Pdk().load(pdkdir / 'layers.json'),12, 4, 2, 3)

    terminals = []

    subinsts = {}

    errors = []

    t_tbl = { "M1": "m1", "M2": "m2", "M3": "m3",
              "M4": "m4", "M5": "m5", "M6": "m6"}

    def add_terminal( netName, layer, b, tag=None):

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        terminals.append( { "netName": netName, "layer": layer, "rect": r})

        def f( gen, value, tag=None):
            # value is in 2x units
            if value%2 != 0:
                txt = f"Off grid:{tag} {layer} {netName} {r} {r[2]-r[0]} {r[3]-r[1]}: {value} (in 2x units) is not divisible by two. {tag}"
                errors.append( txt)
                logger.error( txt)
            else:
                p = gen.clg.inverseBounds( value//2)
                if p[0] != p[1]:
                    txt = f"Off grid:{tag} {layer} {netName} {r} {r[2]-r[0]} {r[3]-r[1]}: {value} doesn't land on grid, lb and ub are: {p}"
                    errors.append( txt)
                    logger.error( txt)

        if layer == "cellarea":
            f( cnv.m1, b.LL.x, "LL.x")
            f( cnv.m1, b.UR.x, "UR.x")
            f( cnv.m2, b.LL.y, "LL.y")
            f( cnv.m2, b.UR.y, "UR.y")
        else:
            if   layer in ["M1", "M3", "M5"]:
                center = (b.LL.x + b.UR.x)//2
            elif layer in ["M2", "M4", "M6"]:
                center = (b.LL.y + b.UR.y)//2
            else:
                center = None
            if center is not None:
                f( cnv.generators[t_tbl[layer]], center, tag)

    if not checkOnly and draw_grid:
        m1_pitch = 2*cnv.pdk['M1']['Pitch']
        m2_pitch = 2*cnv.pdk['M2']['Pitch']
        for ix in range( (hN.width+m1_pitch-1)//m1_pitch):
            x = m1_pitch*ix
            r = [ x-2, 0, x+2, hN.height]
            terminals.append( { "netName": 'm1_grid', "layer": 'M1', "rect": r})

        for iy in range( (hN.height+m2_pitch-1)//m2_pitch):
            y = m2_pitch*iy
            r = [ 0, y-2, hN.width, y+2]
            terminals.append( { "netName": 'm2_grid', "layer": 'M2', "rect": r})

    fa_map = {}
    for n in hN.Nets:
        for c in n.connected:
            if c.type == 'Block':
                cblk = hN.Blocks[c.iter2]
                blk = cblk.instance[cblk.selectedInstance]
                block_name = blk.name
                master_name = blk.master
                pin = blk.blockPins[c.iter]
                formal_name = f"{blk.name}/{pin.name}"
                assert formal_name not in fa_map
                fa_map[formal_name] = n.name

            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name

    for cblk in hN.Blocks:
        blk = cblk.instance[cblk.selectedInstance]
        found = False
        if json_dir is not None:
            pth = pathlib.Path( json_dir + "/" + blk.master + ".json")
            if not pth.is_file():
                logger.info( f"{pth} is not available; not importing subblock rectangles")
            else:
                found = True


        if not found and input_dir is not None:

            logger.debug( f"blk.gdsFile: {blk.gdsFile} {found} {input_dir}")
            p = re.compile( r"^\./Results/(\S+)\.gds$")
            m = p.match( blk.gdsFile)
            if m:
                pth = input_dir / (m.groups()[0] + ".json")
                if not pth.is_file():
                    logger.error( f"{pth} not found in input_dir")
                else:
                    logger.info( f"{pth} found in input_dir")
                    found = True
            else:
                logger.error( f"{blk.gdsFile} does not end in .gds")

        if found:
            with pth.open( "rt") as fp:
                d = json.load( fp)
            # Scale to PnRDB coords (seems like 10x um, but PnRDB is 2x um, so divide by 5
            rational_scaling( d, div=5, errors=errors)

            tr = transformation.Transformation.genTr( blk.orient, w=blk.width, h=blk.height)

            tr2 = transformation.Transformation( oX=blk.placedBox.UR.x - blk.originBox.LL.x,
                                                 oY=blk.placedBox.UR.y - blk.originBox.LL.y)

            tr3 = tr.preMult(tr2)

            logger.info( f"TRANS {blk.master} {blk.orient} {tr} {tr2} {tr3}")

            for term in d['terminals']:
                term['rect'] = tr3.hitRect( transformation.Rect( *term['rect'])).canonical().toList()

            for term in d['terminals']:
                nm = term['netName']
                if nm is not None:
                    formal_name = f"{blk.name}/{nm}"
                    term['netName'] = fa_map.get( formal_name, formal_name)
                if 'pin' in term:
                    del term['pin']
                if 'terminal' in term:
                    assert len(term['terminal']) == 2
                    term['netName'] = f"{blk.name}/{':'.join(term['terminal'])}"
                    term['terminal'] = [f"{blk.name}/{term['terminal'][0]}", term['terminal'][1]]
                if term['layer'] not in ["boundary"]:
                    terminals.append( term)

            if 'subinsts' in d:
                subinsts.update({f'{blk.name}/{nm}': v for nm, v in d['subinsts'].items()})

        if not checkOnly:
            for con in blk.interMetals:
                add_terminal( '!interMetals', con.metal, con.placedBox)

            for via in blk.interVias:
                for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                    add_terminal( '!interVias', con.metal, con.placedBox)

            add_terminal( f"{blk.master}:{blk.name}", 'cellarea', blk.placedBox)

    for n in hN.Nets:
        logger.debug( f"Net: {n.name}")

        def addt( obj, con, tag=None):
            b = con.placedBox
            if obj == n:
                add_terminal( obj.name, con.metal, b, tag=tag)
            else:
                add_terminal( obj, con.metal, b, tag=tag)

        for c in n.connected:
            if c.type == 'Block':
                cblk = hN.Blocks[c.iter2]
                blk = cblk.instance[cblk.selectedInstance]
                block_name = blk.name
                master_name = blk.master
                pin = blk.blockPins[c.iter]
                formal_name = pin.name

                tag = f'Block formal_index: {c.iter},{formal_name} block_index: {c.iter2},{block_name},{master_name}'
                logger.debug( f'\t{tag}')

# 59700, 12210, 59899, 16590


                for con in pin.pinContacts:
                    addt( n, con, "blockPin")
            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name
                tag = f'Terminal formal_index: {c.iter},{terminal_name}'
                logger.debug( f'\t{tag}')
                for con in term.termContacts:
                    pass
#                    addt( n, con)

        for metal in n.path_metal:
            con = metal.MetalRect
            add_terminal( n.name, con.metal, con.placedBox, "path_metal")

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con, "path_via")

        for via in n.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con, "intervia")

    if global_route_json is not None:
        with open(global_route_json, "rt") as fp:
            gr_json = json.load( fp)
        tbl = {}
        for wire in gr_json['wires']:
            nm = wire['net_name']
            if nm not in tbl:
                tbl[nm] = []
            tbl[nm].append(wire)

        for (k,vv) in tbl.items():
            for v in vv:
                for conn in v['connected_pins']:
                    ly = conn['layer']
                    r = conn['rect'][:]
                    for q in [0,1]:
                        r[q], r[q+2] = min(r[q],r[q+2]), max(r[q],r[q+2])

                    if ly != "":
                        d0 = {"netName": k+"_tm", "layer": ly, "rect": r}
                        d1 = {"netName": conn['sink_name'], "layer": ly, "rect": r}
                        logger.info( f"Add two terminals: {d0} {d1}")
                        terminals.append( d0)
                        terminals.append( d1)

                ly = v['layer']
                if 'rect' not in v:
                    logger.error( f"No global route 'rect' in {v}")
                    continue

                r = v['rect'][:]
                for q in [0,1]:
                    r[q], r[q+2] = min(r[q],r[q+2]), max(r[q],r[q+2])

                if  r[0] < r[2] and r[1] < r[3]:
                    logger.error( f"2-dimensional global route {v} {r}")
                if r[0] == r[2] and r[1] == r[3]:
                    logger.error( f"0-dimensional global route {v} {r}")

                logger.info( f"Global route: {k} {ly} {r}")

                for q in [0,1]:
                    if r[q] == r[q+2]:
                        r[q]   -= 20
                        r[q+2] += 20

                terminals.append( {"netName": k+"_gr", "layer": ly, "rect": r})

        if draw_grid:
            m1_pitch = 2*10*cnv.pdk['M1']['Pitch']
            m2_pitch = 2*10*cnv.pdk['M2']['Pitch']
            for ix in range( (hN.width+m1_pitch-1)//m1_pitch):
                x = m1_pitch*ix
                r = [ x-2, 0, x+2, hN.height]
                terminals.append( { "netName": 'm1_bin', "layer": 'M1', "rect": r})

            for iy in range( (hN.height+m2_pitch-1)//m2_pitch):
                y = m2_pitch*iy
                r = [ 0, y-2, hN.width, y+2]
                terminals.append( { "netName": 'm2_bin', "layer": 'M2', "rect": r})

    # Create viewer dictionary

    d = {}

    d["bbox"] = [0,0,hN.width,hN.height]

    d["globalRoutes"] = []

    d["globalRouteGrid"] = []

    d["terminals"] = terminals

    if checkOnly:
        # divide by two be make it be in CellFabric units (nanometer)
        rational_scaling( d, div=2, errors=errors)
        cnv.bbox = transformation.Rect( *d["bbox"])
        cnv.terminals = d["terminals"]
        for inst, parameters in subinsts.items():
            cnv.subinsts[inst].parameters.update(parameters)
        cnv.gen_data(run_pex=extract)


        d['bbox'] = cnv.bbox.toList()
        d['terminals'] = cnv.terminals

        #
        # Experiment for visualizing shorts and opens
        #

        # for (idx,sh) in enumerate(cnv.rd.shorts):
        #     if isinstance( sh, tuple) and len(sh) == 2:
        #         p0, p1 = sh
        #         logger.info( f"SH: {p0} {p1}")
        ## "M0" doesn't always exist
        #         term = { "layer": "M0", "netName": f"SH{idx}_{p0.netName}", "rect": p0.rect}
        #         d['terminals'].append( term)
        #         term = { "layer": "M0", "netName": f"SH{idx}_{p1.netName}", "rect": p1.rect}
        #         d['terminals'].append( term)
        #     else:
        #         logger.error( f"Unknown short type: {sh}")


        # for (nm,lst) in cnv.rd.opens:
        #     logger.info( f"OP: {nm} {lst}")
        #     for (jdx,l) in enumerate(lst):
        #         for (ly,r) in l:
        #             term = { "layer": ly, "netName": f"OP_{nm}_{jdx}", "rect": r}
        #             d['terminals'].append( term)

        # multiply by ten make it be in JSON file units (angstroms) This is a mess!
        rational_scaling( d, mul=10, errors=errors)

        for e in errors:
            cnv.drc.errors.append( e)

        return (cnv, d)
    else:
        # multiply by five make it be in JSON file units (angstroms) This is a mess!
        rational_scaling( d, mul=5, errors=errors)
        return d
