#!/usr/bin/env python

import json
import argparse
import os
import shutil
import copy

from align.gdsconv.gds2lefjson import GDS2_LEF_JSON

ap = argparse.ArgumentParser()
ap.add_argument( "-g", "--gdsdir",  type=str, default="", help='<directory with black box gds files>')
ap.add_argument( "-l", "--layers",  type=str, default="", help='<layers.json file>')
ap.add_argument( "-p", "--primdir", type=str, default="", help="<primitive directory to write outputs>")
ap.add_argument( "-t", "--topodir", type=str, default="", help="<1_topology directory with verilog.json>")
args = ap.parse_args()


if args.layers == "" or args.gdsdir == "" or args.primdir == "" or args.topodir == "":
    ap.print_help()
    exit(0)

if args.topodir[-1] != '/':
    args.topodir += '/'
if args.primdir[-1] != '/':
    args.primdir += '/'
if args.gdsdir[-1] != '/':
    args.gdsdir += '/'

removedmodules = []
for vjson in os.listdir(args.topodir):
    if vjson.endswith(".verilog.json"): 
        with open(args.topodir + vjson) as fp:
            vjdata = json.load(fp)
            fp.close()
            toremove = []
            if "modules" in vjdata:
                for m in vjdata["modules"]:
                    if "instances" in m and len(m["instances"]) == 0 and "constraints" in m:
                        for c in m["constraints"]:
                            if "is_digital" in c and c["is_digital"]:
                                toremove.append(m)
                                removedmodules.append([m["name"], m["parameters"]])
                                break
            for m in toremove:
                vjdata["modules"].remove(m)
            if len(toremove):
                shutil.copy(args.topodir + vjson, args.topodir + vjson + '.bkp')
                with open(args.topodir + vjson, 'wt') as ofp:
                    json.dump(vjdata, ofp, indent = 2)
                toremove = []


for primlib in os.listdir(args.topodir):
    if primlib == "__primitives_library__.json":
        with open(args.topodir + primlib) as fp:
            pdata = json.load(fp)
            fp.close()
            for m in removedmodules:
                if len(m) == 2: pdata.append({"name":m[0], "pins":m[1]})
        if len(removedmodules):
            shutil.copy(args.topodir + primlib, args.topodir + primlib + '.bkp')
            with open(args.topodir + primlib, 'wt') as ofp:
                json.dump(pdata, ofp, indent = 2)
        break

primjson = args.primdir + '__primitives__.json'
if os.path.isfile(primjson):
    with open(primjson) as fp:
        pdata = json.load(fp)
        fp.close()
        if not len(pdata): pdata = dict()
        for m in removedmodules:
            if len(m) == 2: pdata[m[0]] = {"abstract_template_name": m[0], "concrete_template_name": m[0]}
        if len(removedmodules):
            shutil.copy(primjson, primjson + '.bkp')
            with open(primjson, 'wt') as ofp:
                json.dump(pdata, ofp, indent = 2)
else:
    print(f'{primjson} not found')
    exit()

for m in removedmodules:
    gdsfile = args.gdsdir + m[0] + '.gds'
    if os.path.isfile(gdsfile):
        gds2lef = GDS2_LEF_JSON(args.layers, gdsfile, m[0])
        gds2lef.writeLEFJSON(args.primdir)
    else:
        gdsfile = args.gdsdir + m[0].lower() + '.gds'
        if os.path.isfile(gdsfile):
            gds2lef = GDS2_LEF_JSON(args.layers, gdsfile, m[0])
            gds2lef.writeLEFJSON(args.primdir)
        else:
              print(f'leaf {gdsfile} not found')
              exit()
