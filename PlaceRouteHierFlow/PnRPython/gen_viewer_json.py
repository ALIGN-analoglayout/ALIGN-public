#!/usr/bin/env python

import json
import argparse

from pnrdb import *

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Visualize PnR database")
    parser.add_argument( "-d", "--input_dir", type=str, default="Results")
    parser.add_argument( "-b", "--block", type=str, default="telescopic_ota")
    parser.add_argument( "-v", "--variant", type=str, default="0")
    parser.add_argument( "-c", "--check", action='store_true')
    parser.add_argument( "-p", "--pdk_fn", type=str, default="../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json")
    parser.add_argument( "-o", "--output_dir", type=str, default=".")
 
    args = parser.parse_args()

    fn = args.input_dir + "/" + args.block + "_" + args.variant + ".db.json"

    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))

    if args.check:
        cnv = remove_duplicates( hN, pdk_fn=args.pdk_fn)
    else:
        d = gen_viewer_json( hN, pdk_fn=args.pdk_fn)
        with open( args.output_dir + "/" + args.block + "_dr_globalrouting.json", "wt") as fp:
            json.dump( d, fp=fp, indent=2)

