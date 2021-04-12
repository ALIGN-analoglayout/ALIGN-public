from ..cell_fabric import transformation, pdk
from .. import primitive
import itertools
import json
import importlib
import sys
import pathlib
import re
from .toplevel import NType

from .render_placement import gen_transformation

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

def gen_viewer_json( hN, *, pdkdir, draw_grid=False, global_route_json=None, json_dir=None, checkOnly=False, extract=False, input_dir=None, markers=False, toplevel=True):

    logger.info( f'Checking: {hN.name}')

    global_power_names = set( [ n.name for n in hN.PowerNets])

    generator = primitive.get_generator('MOSGenerator', pdkdir)
    # TODO: Remove these hardcoded widths & heights from __init__()
    #       (Height may be okay since it defines UnitCellHeight)
    cnv = generator(pdk.Pdk().load(pdkdir / 'layers.json'),28,12,2,3,1,1,1)

    terminals = []

    subinsts = {}

    errors = []

    def add_terminal( netName, layer, b, tag=None):

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        terminals.append( { "netName": netName, "layer": layer, "rect": r})

        def f( gen, value, tag=None):
            # value is in 2x units
            if value%2 != 0:
                txt = f"Off grid:{tag} {layer} {netName} {r} {r[2]-r[0]} {r[3]-r[1]}: {value} (in 2x units) is not divisible by two."
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
                lyr = layer.lower() if layer.lower() in cnv.generators else layer.upper()
                f( cnv.generators[lyr], center, tag)

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
    for n in itertools.chain( hN.Nets, hN.PowerNets):
        for c in n.connected:
            if c.type == 'Block' or c.type == NType.Block:
                cblk = hN.Blocks[c.iter2]
                blk = cblk.instance[cblk.selectedInstance]
                block_name = blk.name
                master_name = blk.master
                pin = blk.blockPins[c.iter]
                formal_name = f"{blk.name}/{pin.name}"
                assert formal_name not in fa_map
                fa_map[formal_name] = n.name
            elif c.type == 'Terminal' or c.type == NType.Terminal:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert n.name == terminal_name
            else:
                assert False, c.type

    for cblk in hN.Blocks:
        blk = cblk.instance[cblk.selectedInstance]
        found = False
        if json_dir is not None:
            pth = pathlib.Path( json_dir + "/" + blk.master + ".json")
            if not pth.is_file():
                logger.debug( f"{pth} is not available; not importing subblock rectangles")
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
                    logger.debug( f"{pth} found in input_dir")
                    found = True
            else:
                logger.error( f"{blk.gdsFile} does not end in .gds")

        if found:
            with pth.open( "rt") as fp:
                d = json.load( fp)
            # Scale to PnRDB coords (seems like 10x um, but PnRDB is 2x um, so divide by 5
            rational_scaling( d, div=5, errors=errors)

            tr3 = gen_transformation( blk)
            for term in d['terminals']:
                term['rect'] = tr3.hitRect( transformation.Rect( *term['rect'])).canonical().toList()

            for term in d['terminals']:
                nm = term['netName']
                if nm is not None:
                    formal_name = f"{blk.name}/{nm}"
                    default_name = nm if nm in global_power_names else formal_name
                    if nm in ["dummy_gnd_MINUS", "dummy_gnd_PLUS"]:
                        default_name = hN.Gnd.name
                    term['netName'] = fa_map.get( formal_name, default_name)
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

    for n in itertools.chain( hN.Nets, hN.PowerNets):
        logger.debug( f"Net: {n.name}")

        def addt( obj, con, tag=None):
            b = con.placedBox
            if obj == n:
                add_terminal( obj.name, con.metal, b, tag=tag)
            else:
                add_terminal( obj, con.metal, b, tag=tag)

        for c in n.connected:
            if c.type == 'Block' or c.type == NType.Block:
                cblk = hN.Blocks[c.iter2]
                blk = cblk.instance[cblk.selectedInstance]
                block_name = blk.name
                master_name = blk.master
                pin = blk.blockPins[c.iter]
                formal_name = pin.name

                tag = f'Block formal_index: {c.iter},{formal_name} block_index: {c.iter2},{block_name},{master_name}'
                logger.debug( f'\t{tag}')

                for con in pin.pinContacts:
                    addt( n, con, "blockPin")
            elif c.type == 'Terminal' or c.type == NType.Terminal:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name
                tag = f'Terminal formal_index: {c.iter},{terminal_name}'
                logger.debug( f'\t{tag}')
                for con in term.termContacts:
                    pass
#                    addt( n, con)
            else:
                assert False, c.type


        for metal in n.path_metal:
            con = metal.MetalRect
            add_terminal( n.name, con.metal, con.placedBox, "path_metal")

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con, "path_via")

        if hasattr( n, 'interVias'):        
            for via in n.interVias:
                for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                    addt( n, con, "intervia")

    for pg in [hN.Gnd, hN.Vdd]:
        for metal in pg.metals:
            con = metal.MetalRect
            add_terminal( pg.name, con.metal, con.placedBox, "power grid metal")
        for via in pg.vias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                add_terminal( pg.name, con.metal, con.placedBox, "power grid via")

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
                        logger.debug( f"Add two terminals: {d0} {d1}")
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

                logger.debug( f"Global route: {k} {ly} {r}")

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

    logger.debug( f'bbox: {hN.LL.x} {hN.LL.y} {hN.UR.x} {hN.UR.y}')

    d["bbox"] = [hN.LL.x,hN.LL.y,hN.UR.x,hN.UR.y]

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

        nets_allowed_to_be_open = [] if toplevel else global_power_names

        new_d = cnv.gen_data(run_pex=extract,nets_allowed_to_be_open=nets_allowed_to_be_open,postprocess=toplevel)

        d['bbox'] = cnv.bbox.toList()
        d['terminals'] = new_d['terminals']

        # multiply by ten make it be in JSON file units (angstroms) This is a mess!
        rational_scaling( d, mul=10, errors=errors)

        for e in errors:
            cnv.drc.errors.append( e)

        return (cnv, d)
    else:
        # multiply by five make it be in JSON file units (angstroms) This is a mess!
        rational_scaling( d, mul=5, errors=errors)
        return d
