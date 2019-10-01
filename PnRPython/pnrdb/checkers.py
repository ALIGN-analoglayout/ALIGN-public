from cell_fabric import DefaultCanvas, Pdk, transformation
from pprint import pformat
import json
import logging

def gen_viewer_json( hN, *, pdk_fn="../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json", use_orig=False, draw_grid=False, global_route_json=None, json_dir=None, checkOnly=False):
    logger = logging.getLogger(__name__)

    p = Pdk().load( pdk_fn)

    cnv = DefaultCanvas( p)

    d = {}

    d["bbox"] = [0,0,hN.width,hN.height]

    d["globalRoutes"] = []

    d["globalRouteGrid"] = []

    terminals = []

    t_tbl = { "M1": "m1", "M2": "m2", "M3": "m3",
              "M4": "m4", "M5": "m5", "M6": "m6"}

    def add_terminal( netName, layer, b):

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        terminals.append( { "netName": netName, "layer": layer, "rect": r})

        if checkOnly:
            if netName == "!interMetals": return
            if netName == "!interVias": return

        if layer == "cellarea":
            def f( gen, value, tag):
                p = gen.clg.inverseBounds( value)
                if p[0] != p[1]:
                    print( f"Off grid {tag}", layer, netName, p, r)
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
                gen = cnv.generators[t_tbl[layer]]
                p = gen.clg.inverseBounds(center)
                if p[0] != p[1]:
                    print( "Off grid", layer, netName, p, r, r[2]-r[0], r[3]-r[1])

    if not checkOnly and draw_grid:
        m1_pitch = 2*p['M1']['Pitch']
        m2_pitch = 2*p['M2']['Pitch']
        for ix in range( (hN.width+m1_pitch-1)//m1_pitch):
            x = m1_pitch*ix
            r = [ x-1, 0, x+1, hN.height]
            terminals.append( { "netName": 'm1_grid', "layer": 'M1', "rect": r})

        for iy in range( (hN.height+m2_pitch-1)//m2_pitch):
            y = m2_pitch*iy
            r = [ 0, y-1, hN.width, y+1]
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
        if json_dir is not None and blk.isLeaf:
            with open( json_dir + "/" + blk.master + ".json", "rt") as fp:
                d = json.load( fp)
            # Scale to PnRDB coords (seems like 10x um, but PnRDB is 2x um, so divide by 5
            assert all( c % 5 ==0 for c in d['bbox'])
            d['bbox'] = [ c//5 for c in d['bbox']]
            for term in d['terminals']:
                term['rect'] = [ c//5 for c in term['rect']]

            if   blk.orient == "FN":
                tr = transformation.Transformation(                oY=-blk.height, sX=-1       )
            elif blk.orient == "FS":
                tr = transformation.Transformation( oX=-blk.width,                        sY=-1)
            elif blk.orient == "N":
                tr = transformation.Transformation(                                            )
            elif blk.orient == "S":
                tr = transformation.Transformation( oX=-blk.width, oY=-blk.height, sX=-1, sY=-1)
            else:
                assert blk.orient in ["FN","FS","N","S"]

            tr2 = transformation.Transformation( oX=blk.placedBox.UR.x - blk.originBox.LL.x,
                                                 oY=blk.placedBox.UR.y - blk.originBox.LL.y)

            tr3 = tr.preMult(tr2)

            logger.info( f"TRANS {blk.master} {blk.orient} {tr} {tr2} {tr3}")

            for term in d['terminals']:
                term['rect'] = tr3.hitRect( transformation.Rect( *term['rect'])).canonical().toList()
                logger.info( f"{term['rect']}")

            def s( b):
                return f"{b.LL.x} {b.LL.y} {b.UR.x} {b.UR.y}"

            # Determine the transformation
            logger.info( f"{blk.master} {blk.orient} {s(blk.originBox)} {s(blk.placedBox)}")

            for term in d['terminals']:
                if term['layer'] in ["pselect","nwell","poly","fin","active","polycon","LISD","pc","V0","cellarea","nselect"]: continue
                nm = term['netName']
                if nm is not None:
                    formal_name = f"{blk.name}/{nm}"
                    term['netName'] = fa_map.get( formal_name, formal_name)
                if 'pin' in term:
                    del term['pin']
                terminals.append( term)

        def addt( obj, con):
            b = con.originBox if use_orig else con.placedBox
            add_terminal( obj, con.metal, b)

            
        if not checkOnly:

            for con in blk.interMetals:
                addt( '!interMetals', con)

            for via in blk.interVias:
                for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                    addt( '!interVias', con)

            add_terminal( f"{blk.master}:{blk.name}", 'cellarea', blk.originBox if use_orig else blk.placedBox)

    for n in hN.Nets:
        print( f"Net: {n.name}")

        def addt( obj, con):
            b = con.originBox if use_orig else con.placedBox
            if obj == n:
                add_terminal( obj.name, con.metal, b)
            else:
                add_terminal( obj, con.metal, b)

        for c in n.connected:
            if c.type == 'Block':
                cblk = hN.Blocks[c.iter2]
                blk = cblk.instance[cblk.selectedInstance]
                block_name = blk.name
                master_name = blk.master
                pin = blk.blockPins[c.iter]
                formal_name = pin.name

                print( f'\tBlock formal_index: {c.iter},{formal_name} block_index: {c.iter2},{block_name},{master_name}')
                for con in pin.pinContacts:
                    addt( n, con)
            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name
                print( f'\tTerminal formal_index: {c.iter},{terminal_name}')
                for con in term.termContacts:
                    pass
#                    addt( n, con)

        for metal in n.path_metal:
            con = metal.MetalRect
            add_terminal( n.name, con.metal, con.placedBox)

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con)

        for via in n.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con)

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
                    if not isinstance( conn['rect'][0], list):
                        # Seems to be the external terminal case
                        logger.info( f"non-list {conn['rect']}")
                        assert ly == ""
                        rects = [ conn['rect']]
                    else:
                        logger.info( f"list {conn['rect']}")
                        rects = conn['rect']

                    for rect in rects:
                        r = rect[:]
                        for q in [0,1]:
                            r[q], r[q+2] = min(r[q],r[q+2]), max(r[q],r[q+2])

                        d0 = {"netName": k+"_tm", "layer": ly, "rect": r}
                        d1 = {"netName": conn['sink_name'], "layer": ly, "rect": r}
                        logger.info( f"Terminal: {d0} {d1}")
                        terminals.append( d0)
                        terminals.append( d1)
                        

                ly = v['layer']
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
            m1_pitch = 2*10*p['M1']['Pitch']
            m2_pitch = 2*10*p['M2']['Pitch']
            for ix in range( (hN.width+m1_pitch-1)//m1_pitch):
                x = m1_pitch*ix
                r = [ x-1, 0, x+1, hN.height]
                terminals.append( { "netName": 'm1_bin', "layer": 'M1', "rect": r})

            for iy in range( (hN.height+m2_pitch-1)//m2_pitch):
                y = m2_pitch*iy
                r = [ 0, y-1, hN.width, y+1]
                terminals.append( { "netName": 'm2_bin', "layer": 'M2', "rect": r})

    d["terminals"] = terminals

    if checkOnly:
        cnv.bbox = transformation.Rect( *d["bbox"])
        cnv.terminals = d["terminals"]
        cnv.gen_data()

        if len(cnv.drc.errors) > 0:
            pformat(cnv.drc.errors)
        return cnv
    else:
        return d





