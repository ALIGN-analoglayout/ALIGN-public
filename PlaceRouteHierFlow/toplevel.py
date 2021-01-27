#!/usr/bin/env python

# Needed for Pybind11 dynamic executables
import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)

import logging
import colorlog

#level = logging.DEBUG
level = logging.INFO

root = logging.getLogger()
root.setLevel(level)

handler = logging.StreamHandler(sys.stdout)
handler.setLevel(level)

fmt = '[%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s'
datefmt = '%a, %d %b %Y %H:%M:%S' 
if False:
    formatter = logging.Formatter(fmt, datefmt=datefmt)
else:
    formatter = colorlog.ColoredFormatter('%(log_color)s ' + fmt, datefmt=datefmt)
handler.setFormatter(formatter)
root.addHandler(handler)

import PnR

logger = logging.getLogger(__name__)

import pathlib

def toplevel(args):

    assert len(args) == 9

    skip_saving_state = False
    adr_mode = False
    multi_thread = False

    opath = './Results/'
    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]
    if opath[-1] != '/': opath += '/'

    # find directory that args[0] sits in
    binary_directory = str(pathlib.Path(args[0]).parent)

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)
    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()

    TraverseOrder = DB.TraverseHierTree()

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


    new_topnode_idx = 0
    last = TraverseOrder[-1]
    for lidx in range(DB.hierTree[last].numPlacement):
        logger.info( f'lidx: {lidx} new_topnode_idx: {new_topnode_idx} last: {last}')
        PnR.route_top_down( DB, drcInfo, PnR.bbox( PnR.point(0,0),
                                               PnR.point(DB.hierTree[last].PnRAS[0].width,
                                                         DB.hierTree[last].PnRAS[0].height)),
                            PnR.Omark.N, last, new_topnode_idx, lidx,
                            opath, binary_directory, skip_saving_state, adr_mode)

    logger.info( f'Done: new_topnode_idx: {new_topnode_idx} last: {last}')

if __name__ == "__main__":
    toplevel( sys.argv)
