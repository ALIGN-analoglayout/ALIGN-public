#!/usr/bin/env python

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
args = ap.parse_args()

if args.pl_file == "" or args.gds_dir == "":
    ap.print_help()
    exit(0)

print(f"placement verilog : {args.pl_file}")
print(f"gds dir           : {args.gds_dir}")
print(f"top cell          : {args.top_cell}")
print(f"units             : {args.units}")
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
        print(f'working on cell {self._name}')
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
                print(f'{self._name} creating reference of {i._name} at {(oX,oY)} {refl} {angle})')
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
            lname = l.get("abstract_name")
            if lname:
                modu = Module(lname, True)
                modules[modu._name] = modu
        for m in pldata.get("modules"):
            mname = m.get("abstract_name")
            if mname:
                modu = Module(mname)
                for i in m.get("instances"):
                    iname = i.get("abstract_template_name")
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
        print(f'{args.gds_dir} not found')
        exit()
    for j,m in modules.items():
        if not m._leaf:
            continue
        m._fname = args.gds_dir + '/' + j + '.gds.json'
        if not os.path.isfile(m._fname):
            m._fname = args.gds_dir + '/' + j + '.gds'
            if not os.path.isfile(m._fname):
                print(f'leaf {m._fname} not found')
                exit()
            lib = gdspy.GdsLibrary(infile=m._fname)
            m._cell = lib.top_level()[0]
            m._cell.flatten()
            m._added = True
        with open(m._fname) as fp:
            print('found', m._fname)
            leafdata = json.load(fp)
            m._cell = gdspy.Cell(j)
            if 'bgnlib' in leafdata:
                for bl in leafdata['bgnlib']:
                    if 'bgnstr' in bl:
                        for bstr in bl['bgnstr']:
                            if 'elements' in bstr:
                                elements = bstr['elements']
                                for el in elements:
                                    layer = el['layer'] if 'layer' in el else 0
                                    ldata = el['datatype'] if 'datatype' in el else 0
                                    xy = el['xy'] if 'xy' in el else None
                                    if xy and len(xy) == 10:
                                        xmin = min([xy[k] for k in range(0, len(xy), 2)])/args.scale
                                        ymin = min([xy[k] for k in range(1, len(xy), 2)])/args.scale
                                        xmax = max([xy[k] for k in range(0, len(xy), 2)])/args.scale
                                        ymax = max([xy[k] for k in range(1, len(xy), 2)])/args.scale
                                        m._cell.add(gdspy.Rectangle((xmin, ymin), (xmax, ymax), layer=layer, datatype=ldata))
                                    else:
                                        pts = [(xy[k]/args.scale, xy[k + 1]/args.scale) for k in range(0, len(xy), 2)]
                                        m._cell.add(gdspy.Polygon(pts, layer=layer, datatype=ldata))
            m._added = True


for j,m in modules.items():
    for i in m._instances:
        modu = modules.get(i._name)
        if modu:
            i._modu = modu

gdslib = gdspy.GdsLibrary(name=args.top_cell, unit=args.units)
for j,m in modules.items():
    m.add()
    gdslib.add(m._cell)

print(f'writing gds file {args.top_cell}_out.gds')
gdslib.write_gds(args.top_cell + '_out.gds')
