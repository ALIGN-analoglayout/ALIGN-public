#! /usr/bin/env python3

import json
import sys
import math
import argparse
import logging

logger = logging.getLogger(__name__)

from pnrmacro import Macros

ap = argparse.ArgumentParser()
ap.add_argument( "-l", "--lef", type=str, default="", help='<filename.lef>')
ap.add_argument( "-m", "--map", type=str, default="", help='<filename.map>')
ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
args = ap.parse_args()
print("lef : ", args.lef)
print("map : ", args.map)
print("verilog : ", args.verilog)

macros = Macros()
macros.parseLef(args.lef)
macros.print()
