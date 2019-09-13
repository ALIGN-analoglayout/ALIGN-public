from cell_fabric import DefaultCanvas, Pdk, transformation

def check_bbox( b):
    assert b.LL.x < b.UR.x
    assert b.LL.y < b.UR.y

def gen_viewer_json( hN, *, pdk_fn="../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json"):
    p = Pdk().load( pdk_fn)

    cnv = DefaultCanvas( p)

    d = {}

    d["bbox"] = [0,0,hN.width,hN.height]

    d["globalRoutes"] = []

    d["globalRouteGrid"] = []

    terminals = []

    def add_terminal( netName, layer, b):
        check_bbox( b)

        r = [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]
        terminals.append( { "netName": netName, "layer": layer, "rect": r})

        if netName == "!interMetals": return
        if netName == "!interVias": return

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
        if layer == "cellarea":
            p = cnv.m1.clg.inverseBounds( b.LL.x)
            if p[0] != p[1]:
                print( "Off grid LL.x", layer, netName, p, r)
            p = cnv.m1.clg.inverseBounds( b.UR.x)
            if p[0] != p[1]:
                print( "Off grid UR.x", layer, netName, p, r)
            p = cnv.m2.clg.inverseBounds( b.LL.y)
            if p[0] != p[1]:
                print( "Off grid LL.y", layer, netName, p, r)
            p = cnv.m2.clg.inverseBounds( b.UR.y)
            if p[0] != p[1]:
                print( "Off grid UR.y", layer, netName, p, r)

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
            add_terminal( '!interMetals', con.metal, con.placedBox)

        for via in blk.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                add_terminal( '!interVias', con.metal, con.placedBox)

        add_terminal( f"{blk.master}:{blk.name}", 'cellarea', blk.placedBox)

    d["terminals"] = terminals

    return d

def remove_duplicates( hN, *, pdk_fn="../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json"):
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

    cnv.removeDuplicates()

    return cnv
