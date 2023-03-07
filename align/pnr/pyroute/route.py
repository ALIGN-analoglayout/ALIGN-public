#! /usr/bin/env python3

import argparse
from logger import logger

from netlist import Netlist

ap = argparse.ArgumentParser()
ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
ap.add_argument( "-f", "--lef", type=str, default="", help='<lef files>')
ap.add_argument( "-l", "--layers", type=str, default="", help='<layers.json>')
args = ap.parse_args()
print(f"verilog : {args.verilog}")
print(f"LEF     : {args.lef}")
print(f"layers  : {args.layers}")

if args.verilog and args.layers and args.lef:
    nl = Netlist()
    nl.loadVerilog(args.verilog)
    nl.loadLayers(args.layers)
    nl.loadMacros(args.lef)

    nl.print()
