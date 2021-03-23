#!/usr/bin/env python

import logging
import pathlib
import json

# Needed for Pybind11 dynamic executables
import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)

import PnR

logger = logging.getLogger(__name__)

NType = PnR.NType
Omark = PnR.Omark
TransformType = PnR.TransformType

def route_top_down( DB, drcInfo,
                    bounding_box,
                    current_node_ort, idx, lidx,
                    opath, binary_directory, skip_saving_state, adr_mode):

    logger.debug( f'Start of route_top_down {idx=}')

    current_node = DB.CheckoutHierNode(idx) # Make a copy
    DB.hierTree[idx].n_copy += 1
    current_node_name = current_node.name
    current_node.LL = bounding_box.LL
    current_node.UR = bounding_box.UR
    current_node.abs_orient = current_node_ort
    DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, TransformType.Forward)

    for bit, blk in enumerate(current_node.Blocks):
        child_idx = blk.child
        if child_idx == -1: continue
        inst = blk.instance[blk.selectedInstance]
        childnode_orient = DB.RelOrt2AbsOrt( current_node_ort, inst.orient)
        child_node_name = DB.hierTree[child_idx].name
        childnode_bbox = PnR.bbox( inst.placedBox.LL, inst.placedBox.UR)
        new_childnode_idx = 0
        for lidx in range(DB.hierTree[child_idx].numPlacement):
            new_childnode_idx = route_top_down(DB, drcInfo, childnode_bbox, childnode_orient, child_idx, lidx, opath, binary_directory, skip_saving_state, adr_mode)

        DB.CheckinChildnodetoBlock(current_node, bit, DB.hierTree[new_childnode_idx])
        current_node.Blocks[bit].child = new_childnode_idx

    DB.ExtractPinsToPowerPins(current_node)
    PnR.route_single_variant( DB, drcInfo, current_node, lidx, opath, binary_directory, skip_saving_state, adr_mode)

    if not current_node.isTop:
        DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, TransformType.Backward)

    logger.debug( f'Before DB.AppendToHierTree {len(DB.hierTree)=}')
    DB.AppendToHierTree(current_node)
    logger.debug( f'After DB.AppendToHierTree {len(DB.hierTree)=}')
    new_currentnode_idx = len(DB.hierTree) - 1

    for bit,blk in enumerate(current_node.Blocks):
        if blk.child == -1: continue
        DB.SetParentInHierTree( blk.child, 0, new_currentnode_idx)
        logger.debug( f'Set parent of {blk.child} to {new_currentnode_idx} => {DB.hierTree[blk.child].parent[0]=}')

    logger.debug( f'End of route_top_down {len(DB.hierTree)=}')

    return new_currentnode_idx


def toplevel(args):

    assert len(args) == 9

    skip_saving_state = False
    adr_mode = False

    opath = './Results/'
    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]
    if opath[-1] != '/': opath += '/'

    # find directory that args[0] sits in
    binary_directory = str(pathlib.Path(args[0]).parent)

    pathlib.Path(opath).mkdir(parents=True,exist_ok=True)

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)
    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()

    TraverseOrder = DB.TraverseHierTree()

    if not skip_saving_state:
        with open( opath + "__hierTree.json", "wt") as fp:
            json.dump( [DB.CheckoutHierNode(i).name for i in TraverseOrder], indent=2, fp=fp)

    for idx in TraverseOrder:
        logger.info(f'Topo order: {idx}')

        current_node = DB.CheckoutHierNode(idx)

        DB.AddingPowerPins(current_node)

        PRC = PnR.Placer_Router_Cap_Ifc(opath,fpath,current_node,drcInfo,lefData,1,6)

        curr_plc = PnR.PlacerIfc( current_node, numLayout, opath, effort, drcInfo)

        actualNumLayout = curr_plc.getNodeVecSize()
        
        if actualNumLayout != numLayout:
            logger.warning( f'Placer did not provide numLayout ({numLayout} > {actualNumLayout}) layouts')

        for lidx in range(actualNumLayout):
            node = curr_plc.getNode(lidx)
            if node.Guardring_Consts:
                PnR.GuardRingIfc( node, lefData, drcInfo)
            DB.Extract_RemovePowerPins(node)
            DB.CheckinHierNode(idx, node)

        DB.hierTree[idx].numPlacement = actualNumLayout

    last = TraverseOrder[-1]
    new_topnode_indices = []
    for lidx in range(DB.hierTree[last].numPlacement):
        new_topnode_idx = route_top_down( DB, drcInfo,
                                          PnR.bbox( PnR.point(0,0),
                                                    PnR.point(DB.hierTree[last].PnRAS[0].width,
                                                              DB.hierTree[last].PnRAS[0].height)),
                                          Omark.N, last, lidx,
                                          opath, binary_directory, skip_saving_state, adr_mode)
        new_topnode_indices.append(new_topnode_idx)

    return DB
