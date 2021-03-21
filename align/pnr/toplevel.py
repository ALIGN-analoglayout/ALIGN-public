#!/usr/bin/env python

import logging
import pathlib
import json

# Needed for Pybind11 dynamic executables
import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)

import PnR

logger = logging.getLogger(__name__)

def get_NType():
    return PnR.NType

def get_Omark():
    return PnR.Omark

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
    new_topnode_idx = 0
    for lidx in range(DB.hierTree[last].numPlacement):
        new_topnode_idx = PnR.route_top_down( DB, drcInfo, PnR.bbox( PnR.point(0,0),
                                               PnR.point(DB.hierTree[last].PnRAS[0].width,
                                                         DB.hierTree[last].PnRAS[0].height)),
                            PnR.Omark.N, last, lidx,
                            opath, binary_directory, skip_saving_state, adr_mode)


    return DB
