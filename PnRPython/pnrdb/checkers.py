from cell_fabric import DefaultCanvas, Pdk, transformation
from pprint import pformat

def check_bbox( b):
    pass
#    assert b.LL.x < b.UR.x, (b.LL.x,b.UR.x)
#    assert b.LL.y < b.UR.y, (b.LL.y,b.UR.y)

def gen_viewer_json( hN, *, pdk_fn="../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json", use_orig=False, draw_grid=False):
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
        check_bbox( b)

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        terminals.append( { "netName": netName, "layer": layer, "rect": r})

#        if netName == "!interMetals": return
#        if netName == "!interVias": return

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

    if draw_grid:
        m1_pitch = 80
        m2_pitch = 84
        for ix in range( (hN.width+m1_pitch-1)//m1_pitch):
            x = m1_pitch*ix
            r = [ x-1, 0, x+1, hN.height]
            terminals.append( { "netName": 'm1_grid', "layer": 'M1', "rect": r})

        for iy in range( (hN.height+m2_pitch-1)//m2_pitch):
            y = m2_pitch*iy
            r = [ 0, y-1, hN.width, y+1]
            terminals.append( { "netName": 'm2_grid', "layer": 'M2', "rect": r})

    for n in hN.Nets:
        print( n.name)

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
                    addt( n, con)

        for metal in n.path_metal:
            con = metal.MetalRect
            add_terminal( n.name, con.metal, con.placedBox)

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con)

        for via in n.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( n, con)

    for cblk in hN.Blocks:
        blk = cblk.instance[cblk.selectedInstance]
        for con in blk.interMetals:
            addt( '!interMetals', con)

        for via in blk.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                addt( '!interVias', con)

        add_terminal( f"{blk.master}:{blk.name}", 'cellarea', blk.originBox if use_orig else blk.placedBox)

    d["terminals"] = terminals

    return d

def remove_duplicates( hN, *, pdk_fn="../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json"):
    p = Pdk().load( pdk_fn)

    cnv = DefaultCanvas( p)

    cnv.bbox = transformation.Rect(0,0,hN.width,hN.height)

    cnv.terminals = []

    def add_terminal( netName, layer, b):
        check_bbox( b)

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        if layer == "M1":
            p = cnv.m2.clg.inverseBounds( (b.LL.x + b.UR.x)//2)
            if p[0] != p[1]:
                print( "Off grid", layer, netName, p, r)
        if layer == "M2":
            p = cnv.m2.clg.inverseBounds( (b.LL.y + b.UR.y)//2)
            if p[0] != p[1]:
                print( "Off grid", layer, netName, p, r)
        if layer == "M3":
            p = cnv.m3.clg.inverseBounds( (b.LL.x + b.UR.x)//2)
            if p[0] != p[1]:
                print( "Off grid", layer, netName, p, r)
        cnv.terminals.append( { "netName": netName, "layer": layer, "rect": r})

    for n in hN.Nets:
        print( n.name)
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
                    add_terminal( n.name, con.metal, con.placedBox)


            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name
                print( f'\tTerminal formal_index: {c.iter},{terminal_name}')
                for con in term.termContacts:
                    add_terminal( n.name, con.metal, con.placedBox)

        for metal in n.path_metal:
            con = metal.MetalRect
            add_terminal( n.name, con.metal, con.placedBox)

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                add_terminal( n.name, con.metal, con.placedBox)

        for via in n.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                add_terminal( n.name, con.metal, con.placedBox)

    for cblk in hN.Blocks:
        blk = cblk.instance[cblk.selectedInstance]
        for con in blk.interMetals:
            pass
#            add_terminal( '!interMetals', con.metal, con.placedBox)


        for via in blk.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                pass                
#                add_terminal( '!interVias', con.metal, con.placedBox)

    cnv.gen_data()

    if len(cnv.drc.errors) > 0:
        pformat(cnv.drc.errors)

    return cnv
