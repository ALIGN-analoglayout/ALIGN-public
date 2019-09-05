import json

from pnrdb import *

def get_hN(fn="tests/telescopic_ota-freeze.json"):
    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))
        return hN

def check_bbox( b):
    assert b.LL.x == b.UL.x
    assert b.LR.x == b.UR.x

    assert b.LL.y == b.LR.y
    assert b.UL.y == b.UR.y

    assert b.LL.x < b.UR.x
    assert b.LL.y < b.UR.y

def gen_viewer_json( hN):

    d = {}

    d["bbox"] = [0,0,hN.width,hN.height]

    d["globalRoutes"] = []

    d["globalRouteGrid"] = []

    terminals = []

    def add_terminal( netName, layer, b):
        check_bbox( b)
        terminals.append( { "netName": netName,
                            "layer": layer,
                            "rect": [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]})

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


    d["terminals"] = terminals

    return d


from cell_fabric import DefaultCanvas, Pdk, transformation

def test_gen_viewer_json():
    hN = get_hN()
    d = gen_viewer_json( hN)

    with open("__viewer_json","wt") as fp:
        json.dump( d, fp=fp, indent=2)

def remove_duplicates( hN):
    p = Pdk().load( "../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json")

    cnv = DefaultCanvas( p)

    cnv.bbox = transformation.Rect(0,0,hN.width,hN.height)

    cnv.terminals = []

    def add_terminal( netName, layer, b):
        check_bbox( b)
        cnv.terminals.append( { "netName": netName,
                                "layer": layer,
                                "rect": [ b.LL.x, b.LL.y, b.UR.x, b.UR.y]})

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
#            add_terminal( '!interMetals', con.metal, con.placedBox)
            pass

        for via in blk.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
#                add_terminal( '!interVias', con.metal, con.placedBox)
                pass                

    cnv.removeDuplicates()

    return cnv

def test_remove_duplicates():
    hN = get_hN()
    remove_duplicates( hN)
