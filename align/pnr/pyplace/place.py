#! /usr/bin/env python3

import json
import sys
import math
import argparse
from logger import logger

from pnrmacro import Macros
from netlist import Netlist

ap = argparse.ArgumentParser()
ap.add_argument( "-l", "--lef", type=str, default="", help='<filename.lef>')
ap.add_argument( "-m", "--map", type=str, default="", help='<filename.map>')
ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
args = ap.parse_args()
print(f"lef : {args.lef}")
print(f"map : ", args.map)
print(f"verilog : ", args.verilog)

macros = Macros()
macros.parseLef(args.lef)
macros.print()

nl = Netlist()
nl.loadVerilog(args.verilog)
nl.print()
