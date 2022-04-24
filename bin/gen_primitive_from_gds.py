#!/usr/bin/env python

import json
import argparse
import os
import shutil
import copy

from align.gdsconv.gds2primitive import GEN_PRIMITIVE_FROM_GDS

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument( "-g", "--gdsdir",  type=str, default="", help='<directory with black box gds files>')
    ap.add_argument( "-l", "--layers",  type=str, default="", help='<layers.json file>')
    ap.add_argument( "-p", "--primdir", type=str, default="", help="<primitive directory to write outputs>")
    ap.add_argument( "-t", "--topodir", type=str, default="", help="<1_topology directory with verilog.json>")
    args = ap.parse_args()
    
    
    if args.layers == "" or args.gdsdir == "" or args.primdir == "" or args.topodir == "":
        ap.print_help()
        exit(0)

    GEN_PRIMITIVE_FROM_GDS(args.gdsdir, args.layers, args.primdir, args.topodir)
