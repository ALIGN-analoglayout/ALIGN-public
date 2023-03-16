#!/usr/bin/env python

import gdspy
import json
import argparse
import os
import shutil

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument( "-i", "--input",    type=str, default="", help='<gds file name>')
    ap.add_argument( "-p", "--python", type=str, default="", help='<python gds file name>')
    ap.add_argument( "-o", "--output", type=str, default="", help='<output gds file name>')
    args = ap.parse_args()
    
    if args.input == "" or args.python == "":
        ap.print_help()
        exit(0)
    else:
        print(f"gds file     : {args.input}")
        print(f"py gds file  : {args.python}")
        print(f"o/p gds file : {args.output}")
        icell = None
        if not os.path.isfile(args.input):
            print(f'leaf {args.input} not found')
            exit()
        lib = gdspy.GdsLibrary(infile=args.input)
        icell = lib.top_level()[0]
        icell.flatten()
        labels = set()
        for lbl in icell.get_labels():
            labels.add((lbl.layer, lbl.text, int(lbl.position[0] * 1e12)/1e12, int(lbl.position[1] * 1e12)/1e12, lbl.texttype))

        olib = gdspy.GdsLibrary(infile=args.python)
        ocell = olib.top_level()[0]
        for lbl in labels:
            ocell.add(gdspy.Label(lbl[1], (lbl[2], lbl[3]), layer=(lbl[0] + 100)))
        units = gdspy.get_gds_units(args.python)
        cells = set()
        for c in olib.top_level():
            cells.add(c)
            for cell in c.get_dependencies(recursive=True):
                cells.add(cell)
        gdspy.write_gds(args.output, cells = cells, unit = units[0], precision = units[1])

