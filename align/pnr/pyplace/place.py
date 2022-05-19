#! /usr/bin/env python3

import argparse
from logger import logger

from netlist import Netlist

ap = argparse.ArgumentParser()
ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
ap.add_argument( "-p", "--primitives_list", type=str, default="", help='<__primitives__.json>')
ap.add_argument( "-d", "--primitives_dir", type=str, default="", help='<directory with all concrete_primitive.json>')
ap.add_argument( "-l", "--layers", type=str, default="", help='<layers.json>')
args = ap.parse_args()
print(f"verilog : {args.verilog}")
print(f"primitives list : {args.primitives_list}")
print(f"primitives dir : {args.primitives_dir}")
print(f"layers file : {args.layers}")

nl = Netlist()
nl.loadPrimitives(args.primitives_list, args.primitives_dir)
nl.loadVerilog(args.verilog)
nl.loadLayers(args.layers)


nl.print()
nl.place()
