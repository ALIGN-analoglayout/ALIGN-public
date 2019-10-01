#!/usr/bin/env python

import json
import argparse
import logging

from pnrdb import *

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Visualize PnR database")
    parser.add_argument( "-d", "--input_dir", type=str, default="Results")
    parser.add_argument( "-b", "--block", type=str, default="telescopic_ota")
    parser.add_argument( "-v", "--variant", type=str, default="0")
    parser.add_argument( "-c", "--check", action='store_true')
    parser.add_argument( "-p", "--pdk_fn", type=str, default="../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json")
    parser.add_argument( "-o", "--output_dir", type=str, default=".")
    parser.add_argument( "-ifn", "--input_file_name", type=str, default="")
    parser.add_argument( "--use_orig", action='store_true')
    parser.add_argument( "--draw_grid", action='store_true')
    parser.add_argument( "--verbose", action='store_true')
    parser.add_argument( "--global_route_json", type=str, default=None)
 
    args = parser.parse_args()

    logging.basicConfig(level=logging.CRITICAL)

    logger = logging.getLogger()
    if ( args.verbose):
        logger.setLevel( logging.INFO)

    fn = args.input_dir + "/" + args.block + "_" + args.variant + ".db.json"
    if args.input_file_name:
        fn = args.input_dir + "/" + args.input_file_name

    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))

    if args.check:
        cnv = remove_duplicates( hN, pdk_fn=args.pdk_fn)
    else:
        d = gen_viewer_json( hN, pdk_fn=args.pdk_fn, use_orig=args.use_orig, draw_grid=args.draw_grid, global_route_json=args.global_route_json)
        with open( args.output_dir + "/" + args.block + "_" + args.variant + "_dr_globalrouting.json", "wt") as fp:
            json.dump( d, fp=fp, indent=2)

