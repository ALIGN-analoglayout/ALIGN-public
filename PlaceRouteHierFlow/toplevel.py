#!/usr/bin/env python

import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
import PnR
from PnR import *

import logging

root = logging.getLogger()
root.setLevel(logging.DEBUG)

logger = logging.getLogger(__name__)
handler = logging.StreamHandler(sys.stdout)
handler.setLevel(logging.DEBUG)
formatter = logging.Formatter('[%(asctime)s] %(levelname)s [%(filename)s.%(funcName)s:%(lineno)d] %(message)s', datefmt='%a, %d %b %Y %H:%M:%S')
handler.setFormatter(formatter)
root.addHandler(handler)

def toplevel(args):

    assert len(args) == 9

    opath = './Results/'
    fpath,lfile,vfile,mfile,dfile,topcell = args[1:7]
    numLayout,effort = [ int(x) for x in args[7:9]]

    if fpath[-1] == '/': fpath = fpath[:-1]
    if opath[-1] != '/': opath += '/'

    # find directory that args[0] sits in; hack for now as current directory
    binary_directory = "."

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)
    DB.PrintHierTree()

    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()

    TraverseOrder = DB.TraverseHierTree()

    for idx in TraverseOrder:
        logger.info(f'Topo order: {idx}')

        current_node = DB.CheckoutHierNode(idx)

        save_state(DB,current_node, 0, opath, "FOO", "BAR", False)

        DB.AddingPowerPins(current_node)

        save_state(DB,current_node, 0, opath, "FOO", "BAR_PP", False)

        curr_plc = PlacerIfc( current_node, numLayout, opath, effort, drcInfo)
        nodeVec = curr_plc.get()
        
        for placed_node in nodeVec:
            print(placed_node)
        


if __name__ == "__main__":
    toplevel( sys.argv)
