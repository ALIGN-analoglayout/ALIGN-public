#!/usr/bin/env python

import json
import argparse
#import cProfile

from align.pnr import hierNode, gen_viewer_json

import logging

def main():
    parser = argparse.ArgumentParser( description="Visualize PnR database")
    parser.add_argument( "-d", "--input_dir", type=str, default="Results")
    parser.add_argument( "-b", "--block", type=str, default="telescopic_ota")
    parser.add_argument( "-v", "--variant", type=str, default="0")
    parser.add_argument( "-c", "--check", action='store_true')
    parser.add_argument( "-m", "--markers", action='store_true')
    parser.add_argument( "-e", "--extract", action='store_true')
    parser.add_argument( "-t", "--tag", type=str, default="")
    parser.add_argument( "-p", "--pdk", type=str, default="../pdks/FinFET14nm_Mock_PDK/")
    parser.add_argument( "-o", "--output_dir", type=str, default=".")
    parser.add_argument( "-ifn", "--input_file_name", type=str, default="")
    parser.add_argument( "--draw_grid", action='store_true')
    parser.add_argument( "-l", "--log", dest="logLevel", choices=['DEBUG','INFO','WARNING','ERROR','CRITICAL'], default='INFO', help="Set the logging level (default: %(default)s)")
    parser.add_argument( "--global_route_json", type=str, default=None)
    parser.add_argument( "--json_dir", type=str, default=None)
 
    args = parser.parse_args()
    logging.getLogger().setLevel(logging.getLevelName(args.logLevel))

    fn = args.input_dir + "/" + args.block + "_" + args.variant + ".db.json"

    if args.input_file_name:
        fn = args.input_dir + "/" + args.input_file_name

    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))

    res = gen_viewer_json( hN, pdk=args.pdk, draw_grid=args.draw_grid, global_route_json=args.global_route_json, json_dir=args.json_dir, checkOnly=args.check, extract=args.extract, input_dir=args.input_dir, markers=args.markers)

    if not args.check:
        d = res
        with open( args.output_dir + "/" + args.block + "_" + args.variant + "_dr_globalrouting.json", "wt") as fp:
            json.dump( d, fp=fp, indent=2)
    else:
        cnv, d = res
        with open( args.json_dir + "/" + args.block + ".json", "wt") as fp:
            json.dump( d, fp=fp, indent=2)
        if args.markers:
            with open( args.output_dir + "/" + args.block + "_" + args.variant + "_dr_globalrouting.json", "wt") as fp:
                json.dump( d, fp=fp, indent=2)
        if args.extract:
            print(args.output_dir + "/" + args.block + ".cir")
            with open(args.output_dir + "/" + args.block + ".cir", 'wt') as fp:
                cnv.pex.writePex(fp)

if __name__ == "__main__":
    #cProfile.run("main()")
    main()
