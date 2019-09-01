import json

from pnrdb import *

def get_hN():
    with open("tests/telescopic_ota-freeze.json","rt") as fp:
        hN = hierNode(json.load(fp))
        return hN

def check_bbox( b):
    assert b.LL.x == b.UL.x
    assert b.LR.x == b.UR.x

    assert b.LL.y == b.LR.y
    assert b.UL.y == b.UR.y

    assert b.LL.x < b.UR.x
    assert b.LL.y < b.UR.y

    assert len(b.polygon) == 4 or len(b.polygon) == 0


def test_A():
    hN = get_hN()
    assert hN.name == "telescopic_ota"

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
                    check_bbox( con.placedBox)
                    print( f"\t\tpinContact {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")

                for con in blk.interMetals:
                    check_bbox( con.placedBox)
                    print( f"\t\tinterMetal {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")

                for via in blk.interVias:
                    for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                        check_bbox( con.placedBox)
                        print( f"\t\tinterVia {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")


            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name
                print( f'\tTerminal formal_index: {c.iter},{terminal_name}')
                for con in term.termContacts:
                    check_bbox( con.placedBox)
                    print( f"\t\t{con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")

        for metal in n.path_metal:
            con = metal.MetalRect
            check_bbox( con.placedBox)
            print( f"\tpath_metal {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")

        for via in n.path_via:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                check_bbox( con.placedBox)
                print( f"\tpath_via {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")

        for via in n.interVias:
            for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
                check_bbox( con.placedBox)
                print( f"\tinterVia {con.placedBox.LL._d} {con.placedBox.UR._d} {con.metal}")





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

                for con in blk.interMetals:
                    add_terminal( n.name, con.metal, con.placedBox)

                for via in blk.interVias:
                    for con in [via.UpperMetalRect,via.LowerMetalRect,via.ViaRect]:
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

    d["terminals"] = terminals

    return d

def test_gen_viewer_json():
    hN = get_hN()
    d = gen_viewer_json( hN)

    with open("__viewer_json","wt") as fp:
        json.dump( d, fp=fp, indent=2)
