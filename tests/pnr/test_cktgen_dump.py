import json
import pathlib
import os
import pytest

from align.pnr import *

import logging
logger = logging.getLogger(__name__)

mydir = pathlib.Path(__file__).resolve().parent

def check_wire_widths( terminals, sc):
    for term in terminals:
        assert 'net_name' in term or 'netName' in term
        assert 'layer' in term
        assert 'rect' in term
        # don't want M1 and M2 on the interface
        if term['layer'] in ['M2','V2','M3']:
            if term['layer'] == 'M3':
                r = term['rect']
                width = r[2]-r[0]
                assert width == sc*40, width
            if term['layer'] == 'M2':
                r = term['rect']
                width = r[3]-r[1]
                assert width == sc*32, width


def aux(design, subdesign=None):
    if subdesign is None:
        subdesign = design

    # Generate this above formatted file from PnRDB data
    rdir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / design / "3_pnr" / "Results"
    assert rdir.is_dir()

    json_dir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / design / "2_primitives"
    assert json_dir.is_dir()

    alt_json_dir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / design / "3_pnr"
    assert alt_json_dir.is_dir()

    with (rdir / f"{subdesign}_0.db.json").open("rt") as fp:
        hN = hierNode(json.load(fp))

    assert hN.name == subdesign


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

        if not found:
            pth = alt_json_dir / (blk.master + "_0.json") 
            if not pth.is_file():
                logger.warning( f"{pth} is not available; not importing subblock rectangles")
            else:
                logger.info( f"{pth} found in alternative path (sub-block)")
                found = True

        assert found
        with pth.open("rt") as fp:
            leaves[blk.master] = json.load(fp)

    
    result = {}
    result['nm'] = hN.name
    result['bbox'] = [0,0,hN.width,hN.height]
    result['leaves'] = []
    result['instances'] = []

# Everything is in Angstroms
    for k,leaf in leaves.items():
        check_wire_widths( leaf['terminals'], 10)

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
            # don't want M1 and M2 on the interface
            if term1['layer'] in ['M2','V2','M3']:
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
                pin = blk.blockPins[c.iter]
                if blk.name not in fa_map: fa_map[blk.name] = {}
                assert pin.name not in fa_map[blk.name]
                fa_map[blk.name][pin.name] = n.name

            else:
                term = hN.Terminals[c.iter]
                terminal_name = term.name
                assert terminal_name == n.name


    for k,leaf in leaves.items():
        check_wire_widths( leaf['terminals'], 10)

#
# Only scale once
#
    for (k,v) in leaves.items():
        # Scale to PnRDB coords (seems like 10x um, but PnRDB is 2x um, so divide by 5
        rational_scaling( v, div=5)

    for k,leaf in leaves.items():
        check_wire_widths( leaf['terminals'], 2)

#
# Now in 2x nanometers
#

    for cblk in hN.Blocks:
        inst = {}

        blk = cblk.instance[cblk.selectedInstance]

        print( "working on", blk.master)

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
    mul=5

    result['bbox'] = [ mul*c for c in result['bbox']]
    for leaf in result['leaves']:
        rational_scaling( leaf, mul=mul)

    for leaf in result['leaves']:
        check_wire_widths( leaf['terminals'], 10)

    for inst in result['instances']:
        inst['transformation']['oX'] *= mul
        inst['transformation']['oY'] *= mul

    with open( mydir / f"__json_{subdesign}_dump", "wt") as fp:
        json.dump( result, fp, indent=2)

#
# Read in global routing file, modify and write out
#
    with ( rdir / f"{subdesign}_GcellGlobalRoute_0.json" ).open("rt") as fp:
        grs = json.load( fp)

    newWires = []

    hWires = {"M2": "metal2", "M4": "metal4", "M6": "metal4"}
# map M7 to metal5
    vWires = {"M1": "metal1", "M3": "metal3", "M5": "metal5", "M7": "metal5"}

    wire_widths = { "metal1": 320, "metal2": 320, "metal3": 400, "metal4": 320, "metal5": 640}

    layer_map = dict( list(hWires.items()) + list(vWires.items()))

    for wire in grs['wires']:
        newLayer = layer_map[wire['layer']]                     
        width = wire_widths[newLayer]            
        newWire = { 'layer': newLayer, 'net_name': wire['net_name'], 'width': width, 'connected_pins': []}

        if wire['layer'] in hWires:
            bin_ = 10*84*2
        elif wire['layer'] in vWires:
            bin_ = 10*80*2
        else:
            assert False, wire['layer']
        
        newWire['rect'] = [ c//bin_ for c in wire['rect']]    

        r = newWire['rect']

        assert r[0] == r[2] or r[1] == r[3]

        if r[0] != r[2] or r[1] != r[3]:
            newWires.append(newWire)

    newGRs = { 'wires': newWires}
    with open( mydir / f"__json_{subdesign}_gr", "wt") as fp:
        json.dump( newGRs, fp=fp, indent=2)

def results_directory_missing(design):
    '''
    This function will return true
    if dependency is not satisfied
    '''
    if 'ALIGN_WORK_DIR' not in os.environ: return True
    assert design, 'Function expects design name'
    rdir = pathlib.Path( os.environ["ALIGN_WORK_DIR"]) / design / "3_pnr" / "Results"
    return not rdir.is_dir()

@pytest.mark.skipif(results_directory_missing("five_transistor_ota"),
                    reason='Necessary test collateral has not been built')
def test_A():
    aux( "five_transistor_ota", "five_transistor_ota")

@pytest.mark.skipif(results_directory_missing("switched_capacitor_filter"),
                    reason='Necessary test collateral has not been built')
def test_B():
    aux( "switched_capacitor_filter", "telescopic_ota")

@pytest.mark.skipif(results_directory_missing("telescopic_ota"),
                    reason='Necessary test collateral has not been built')
def test_B2():
    aux( "telescopic_ota", "telescopic_ota")

@pytest.mark.skipif(results_directory_missing("cascode_current_mirror_ota"),
                    reason='Necessary test collateral has not been built')
def test_C():
    aux( "cascode_current_mirror_ota", "CASCODED_CMC_PMOS")
    aux( "cascode_current_mirror_ota", "cascode_current_mirror_ota")

