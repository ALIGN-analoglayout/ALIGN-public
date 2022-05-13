#!/usr/bin/env python3

import numpy
import gdspy
import json
import argparse
import os

ap = argparse.ArgumentParser()
ap.add_argument( "-p", "--pl_file", type=str, default="", help='<filename.placement_verilog.json>')
ap.add_argument( "-g", "--gds_dir", type=str, default="", help='<dir with all leaf gds files>')
ap.add_argument( "-t", "--top_cell", type=str, default="library", help='<top cell>')
ap.add_argument( "-u", "--units", type=float, default=1e-6, help='<units in m>')
ap.add_argument( "-s", "--scale", type=float, default=2e3, help='<scale>')
ap.add_argument( "-l", "--layers", type=str, default="", help='<layers.json>')
ap.add_argument( "-d", "--deff", type=str, default="", help='<route def file>')
ap.add_argument( "-o", "--out_dir", type=str, default="./", help='<output dir>')
args = ap.parse_args()
#print(f"placement verilog : {args.pl_file}")
#print(f"gds dir           : {args.gds_dir}")
#print(f"top cell          : {args.top_cell}")
#print(f"units             : {args.units}")
#print(f"layers.json       : {args.layers}")
#print(f"route def file    : {args.deff}")

if args.pl_file == "" or args.gds_dir == "" or args.layers == "" or args.deff == "":
    ap.print_help()
    exit()

class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._oX = oX 
        self._oY = oY
        self._sX = sX
        self._sY = sY
    def __str__(self):
        return f'({str(self._oX)} {str(self._oY)} {str(self._sX)} {str(self._sY)})'

class Instance:
    def __init__(self, name = "", tr = Transform()):
        self._name = name
        self._tr   = tr
        self._modu = None
    def __str__(self):
        return f'{self._name} {str(self._tr)}'

class Module:
    def __init__(self, name = "", leaf = False):
        self._name      = name
        self._instances = list()
        self._added     = False
        self._leaf      = leaf
        self._fname     = ""
        self._cell      = None
    def __str__(self):
        s = f"{self._name} '{self._fname}' {self._cell}"
        for i in self._instances:
            s += f' [{str(i)} {i._modu._name}]'
        return s
    def add(self):
        #print(f'working on cell {self._name}')
        for i in self._instances:
            if i._modu:
                if not i._modu._added:
                    i._modu.add()
                bbox = i._modu._cell.get_bounding_box()
                angle, refl = 0, False
                oX, oY = i._tr._oX/args.scale, i._tr._oY/args.scale
                if i._tr._sX < 0:
                    angle = 180
                    refl = (i._tr._sY > 0)
                else:
                    refl = (i._tr._sY < 0)
                #print(f'{self._name} creating reference of {i._name} at {(oX,oY)} {refl} {angle})')
                ref = gdspy.CellReference(i._modu._cell, (oX, oY), x_reflection = refl, rotation = angle)
                if not self._cell:
                    self._cell = gdspy.Cell(self._name)
                self._cell.add(ref)
        self._added = True

modules = dict()
if args.pl_file:
    with open(args.pl_file) as fp:
        pldata = json.load(fp)
        for l in pldata.get("leaves"):
            lname = l.get("concrete_name")
            if lname:
                modu = Module(lname, True)
                modules[modu._name] = modu
        for m in pldata.get("modules"):
            mname = m.get("concrete_name")
            if mname:
                modu = Module(mname)
                for i in m.get("instances"):
                    iname = i.get("concrete_template_name")
                    trstr = i.get("transformation")
                    tr = Transform()
                    if trstr:
                        tr._oX, tr._oY = trstr["oX"], trstr["oY"]
                        tr._sX, tr._sY = trstr["sX"], trstr["sY"]
                    if iname:
                        modu._instances.append(Instance(iname, tr))
                modules[modu._name] = modu

gdscell = dict()
if (args.gds_dir):
    if not os.path.isdir(args.gds_dir):
        #print(f'{args.gds_dir} not found')
        exit()
    for j,m in modules.items():
        if not m._leaf:
            continue
        m._fname = args.gds_dir + '/' + j + '.gds'
        if not os.path.isfile(m._fname):
            #print(f'leaf {m._fname} not found')
            exit()
        lib = gdspy.GdsLibrary(infile=m._fname)
        m._cell = lib.top_level()[0]
        m._cell.flatten()
        m._added = True


for j,m in modules.items():
    for i in m._instances:
        modu = modules.get(i._name)
        if modu:
            i._modu = modu

gdslib = gdspy.GdsLibrary(name=args.top_cell, unit=args.units)

layers = dict()
if args.layers:
    with open(args.layers) as fp:
        layerdata = json.load(fp)
        if "Abstraction" in layerdata:
            for l in layerdata["Abstraction"]:
                if "Layer" in l and "GdsLayerNo" in l:
                    layer = l["Layer"]
                    glno1 = l["GdsLayerNo"]
                    if "GdsDatatype" in l and "Draw" in l["GdsDatatype"]:
                        glno2 = l["GdsDatatype"]["Draw"]
                    else:
                        glno2 = 0
                    layers[layer] = (glno1,glno2)

        
for j,m in modules.items():
    m.add()
    gdslib.add(m._cell)

if args.deff:
    with open(args.deff) as fp:
        innets = False
        infills = False
        sca = args.scale
        layeridx = None
        for line in fp:
            line.strip()
            if "NETS" in line:
                if "END" in line:
                    innets = False
                else:
                    innets = True
            if "FILLS" in line:
                if "END" in line:
                    infills = False
                else:
                    infills = True
            if infills:
                if "LAYER" in line:
                    s = line.split()
                    if len(s) > 1:
                        if s[1] == "LAYER":
                            layeridx = layers[s[2]]
                if "RECT" in line and layeridx:
                    s = line.split()
                    if len(s) > 8:
                        if s[0] == "RECT":
                            index = 0
                        rect = [float(s[index + 2])/sca, float(s[index + 3])/sca, float(s[index + 6])/sca, float(s[index + 7])/sca]
                        l = layeridx
                        #print("fill shape : ", rect)
                        if args.top_cell in modules:
                            modules[args.top_cell]._cell.add(gdspy.Rectangle((rect[0], rect[1]), (rect[2], rect[3]), layer=l[0], datatype=l[1]))
            if innets and "RECT" in line:
                s = line.split()
                if len(s) > 10:
                    index = 0
                    if s[0] == "RECT":
                        index = 0
                    if s[1] == "RECT":
                        index = 1
                    layer = s[index + 1]
                    rect = [float(s[index + 3])/sca, float(s[index + 4])/sca, float(s[index + 7])/sca, float(s[index + 8])/sca]
                    l = layers[layer]
                    if args.top_cell in modules:
                        #print(rect)
                        modules[args.top_cell]._cell.add(gdspy.Rectangle((rect[0], rect[1]), (rect[2], rect[3]), layer=l[0], datatype=l[1]))
            

        

gdslib.write_gds(args.out_dir + '/' + args.top_cell + '.gds')
