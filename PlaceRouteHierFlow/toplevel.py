#!/usr/bin/env python

# Needed for Pybind11 dynamic executables
import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)

import logging
import colorlog

root = logging.getLogger()
root.setLevel(logging.INFO)

logger = logging.getLogger(__name__)
handler = logging.StreamHandler(sys.stdout)
handler.setLevel(logging.INFO)
#formatter = logging.Formatter('[%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s', datefmt='%a, %d %b %Y %H:%M:%S')
#handler.setFormatter(formatter)
handler.setFormatter(colorlog.ColoredFormatter('%(log_color)s [%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s', datefmt='%a, %d %b %Y %H:%M:%S'))
root.addHandler(handler)

import PnR

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

    # find directory that args[0] sits in; hack for now as current directory
    binary_directory = "."

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)

    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()

    TraverseOrder = DB.TraverseHierTree()

    for idx in TraverseOrder:
        logger.info(f'Topo order: {idx}')

        current_node = DB.CheckoutHierNode(idx)

        DB.AddingPowerPins(current_node)

        curr_plc = PnR.PlacerIfc( current_node, numLayout, opath, effort, drcInfo)

        actualNumLayout = curr_plc.getNodeVecSize()
        
        if actualNumLayout != numLayout:
            logger.warning( f'Placer did not provide numLayout ({numLayout} > {actualNumLayout}) layouts')

        for lidx in range(actualNumLayout):
            node = curr_plc.getNode(lidx)
            if node.Guardring_Consts:
                PnR.GuardRingIfc( node, lefData, drcInfo)
        
        for lidx in range(actualNumLayout):
            node = curr_plc.getNode(lidx)
            DB.Extract_RemovePowerPins(node)
            DB.CheckinHierNode(idx, node)

        DB.hierTree[idx].numPlacement = actualNumLayout


    new_topnode_idx = 0
    last = TraverseOrder[-1]
    for lidx in range(DB.hierTree[last].numPlacement):
        PnR.route_top_down( DB, drcInfo, PnR.bbox( PnR.point(0,0),
                                               PnR.point(DB.hierTree[last].PnRAS[0].width,
                                                         DB.hierTree[last].PnRAS[0].height)),
                            PnR.Omark.N, last, new_topnode_idx, lidx,
                            opath, binary_directory, skip_saving_state, adr_mode)


if __name__ == "__main__":
    toplevel( sys.argv)
