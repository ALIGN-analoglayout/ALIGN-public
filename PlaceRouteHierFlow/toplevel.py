#!/usr/bin/env python

import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
import PnR
from PnR import *

def toplevel(args):

    assert len(args) == 9

    opath = './Results/'
    fpath = args[1]
    lfile = args[2]
    vfile = args[3]
    mfile = args[4]
    dfile = args[5]
    topcell = args[6]
    numLayout = int(args[7])
    effort = int(args[8])

    if fpath[-1] == '/': fpath = fpath[:-1]
    if opath[-1] != '/': opath += '/'

    # find directory that args[0] sits in
    binary_directory = args[0]

    DB = PnR.PnRdatabase( fpath, topcell, vfile, lfile, mfile, dfile)
    drcInfo = DB.getDrc_info()
    lefData = DB.checkoutSingleLEF()


if __name__ == "__main__":
    toplevel( sys.argv)
