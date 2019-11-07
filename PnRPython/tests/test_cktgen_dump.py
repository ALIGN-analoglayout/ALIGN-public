
import pnrdb
import json
import pathlib
import os
from pnrdb import *

def test_A():
    """
{
   "nm": "telescopic_ota",
   "bbox": [ llx, lly, urx, ury],
   "leaves": [
       {
           "template_name": "",
           "bbox": [ llx, lly, urx, ury],
           "terminals": [
              {
                  "net_name": "",
                  "layer": "",
                  "rect": [llx, lly, urx, ury]
              }
           ]
       }
   ],
   "instances": [
       {
           "template_name": "",
           "instance_name": "",
           "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1},
           "formal_actual_map": {
               "formal1": "",
               "formal2": "",
           }  
       }
   ]
}
"""
    # Generate this above formatted file from PnRDB data
    rdir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / "switched_capacitor_filter/pnr_output/Results"
    assert rdir.is_dir()

    json_dir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / "switched_capacitor_filter/pnr_output/inputs"
    assert json_dir.is_dir()

    with (rdir / "telescopic_ota_0.post_gr.db.json").open("rt") as fp:
        hN = hierNode(json.load(fp))

    assert hN.name == "telescopic_ota"


    leaves = {}

    for cblk in hN.Blocks:
        blk = cblk.instance[cblk.selectedInstance]
        if blk.master in leaves: continue

        print( blk.master)

        found = False
        pth = json_dir / (blk.master + ".json") 
        if not pth.is_file():
            logger.warning( f"{pth} is not available; not importing subblock rectangles")
        else:
            found = True

        assert found
        with pth.open("rt") as fp:
            leaves[blk.master] = json.load(fp)

    
    result = {}
    result['nm'] = hN.name
    result['bbox'] = [0,0,hN.width,hN.height]
    result['leaves'] = []
    result['instances'] = []

    for k,src in sorted(leaves.items()):
        leaf = {}
        leaf['template_name'] = k
        leaf['bbox'] = src['bbox']
        leaf['terminals'] = []
        for term in src['terminals']:
            assert 'netName' in term
            assert 'layer' in term
            assert 'rect' in term
            term1 = { 'net_name': term['netName'],
                      'layer': term['layer'],
                      'rect': term['rect']
            }
            if term1['layer'] in ['M1','V1','M2','V2','M3']:
                leaf['terminals'].append(term1)

        result['leaves'].append(leaf)


#
# Update leaves with new dictionary
#
    leaves = {}
    for v in result['leaves']:
        k = v['template_name']
        leaves[k] = v

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
                if blk.name not in fa_map: fa_map[blk.name] = {}
                assert pin.name not in fa_map[blk.name]
                fa_map[blk.name][pin.name] = n.name

            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name

#    print(result['leaves'])

    assert len(result['leaves']) == 5

    for cblk in hN.Blocks:
        inst = {}

        blk = cblk.instance[cblk.selectedInstance]

        d = leaves[blk.master]

        # Scale to PnRDB coords (seems like 10x um, but PnRDB is 2x um, so divide by 5
        rational_scaling( d, div=5)

        tr = transformation.Transformation.genTr( blk.orient, w=blk.width, h=blk.height)

        tr2 = transformation.Transformation( oX=blk.placedBox.UR.x - blk.originBox.LL.x,
                                             oY=blk.placedBox.UR.y - blk.originBox.LL.y)

        tr3 = tr.preMult(tr2)

        print( blk.name, blk.master, tr3)

        logger.info( f"TRANS {blk.master} {blk.orient} {tr} {tr2} {tr3}")
        inst['template_name'] = blk.master
        inst['instance_name'] = blk.name
        inst['transformation'] = { "oX": tr3.oX, "oY": tr3.oY, "sX": tr3.sX, "sY": tr3.sY}

        assert blk.name in fa_map
        
        inst['formal_actual_map'] = fa_map[blk.name]

        result['instances'].append( inst)

#
# Need to scale result by 5 to take it back to angstroms
#

    with open( "tests/__json_telescopic_ota_dump", "wt") as fp:
        json.dump( result, fp, indent=2)

