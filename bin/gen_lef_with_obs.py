#! /usr/bin/env python

import json
import sys
import math
import argparse

ap = argparse.ArgumentParser()
ap.add_argument( "-l", "--layers", type=str, default="", help='<layers.json>')
ap.add_argument( "-g", "--gds",   type=str, default="", help='<gds.json file>')
ap.add_argument( "-f", "--lef",   type=str, default="", help='<.lef file>')
ap.add_argument( "-u", "--use_layers",   nargs="*", type=str, default=[], help='list of layers to add obstacles (all if empty)')
args = ap.parse_args()
print("layers.json   : ", args.layers)
print("gds.json file : ", args.gds)
print(".lef file     : ", args.lef)
if args.use_layers:
  print ("layers        : ", args.use_layers)

if args.layers == "" or args.gds == "" or args.lef == "":
  ap.print_help()
  exit(0)

class Point:
  def __init__(self, x=None, y=None):
    self._x = x
    self._y = y

  def toList(self):
    return [self._x, self._y]

  def __repr__( self):
    return str(self.toList())


class Rect:
  def __init__( self, llx=None, lly=None, urx=None, ury=None):
    self._ll = Point(llx, lly)
    self._ur = Point(urx, ury)
    if (llx != None and urx != None):
      self._ll._x = min(llx, urx)
      self._ur._x = max(llx, urx)
    if (lly != None and ury != None):
      self._ll._y = min(lly, ury)
      self._ur._y = max(lly, ury)

  def toList( self):
    return [self._ll.toList(), self._ur.toList()]

  def __repr__( self):
    return str(self.toList())

  def overlaps(self, r, strict = False):
    if strict:
      return self._ll._x < r._ur._x and self._ur._x > r._ll._x and \
        self._ll._y < r._ur._y and self._ur._y > r._ll._y
    else:
      return self._ll._x <= r._ur._x and self._ur._x >= r._ll._x and \
        self._ll._y <= r._ur._y and self._ur._y >= r._ll._y

  def toString(self, unit):
    x1 = math.trunc(self._ll._x * 10000/unit)/10000
    if (x1 == math.trunc(x1)): x1 = math.trunc(x1)
    y1 = math.trunc(self._ll._y * 10000/unit)/10000
    if (y1 == math.trunc(y1)): y1 = math.trunc(y1)
    x2 = math.trunc(self._ur._x * 10000/unit)/10000
    if (x2 == math.trunc(x2)): x2 = math.trunc(x2)
    y2 = math.trunc(self._ur._y * 10000/unit)/10000
    if (y2 == math.trunc(y2)): y2 = math.trunc(y2)
    tmpstr = str(x1) + ' ' + str(y1) + ' ' + str(x2) + ' ' + str(y2)
    return tmpstr


layerData = dict()
layers = set()
if (args.layers):
  with open (args.layers, 'rt') as ifile:
    layerJSON = json.load(ifile)
    if ("Abstraction" in layerJSON):
      for layer in layerJSON["Abstraction"]:
        if "Layer" in layer and "GdsLayerNo" in layer:
          layerData[layer["GdsLayerNo"]] = layer["Layer"]
          layers.add(layer["Layer"])

gdsUnits = 1
layerRects = dict()
if (args.gds):
  with open (args.gds, 'rt') as ifile:
    data = json.load (ifile)
    if 'bgnlib' in data:
      for lib in data['bgnlib']:
        if 'units' in lib:
          units = lib['units']
          if len(units) > 1:
            gdsUnits = units[1]
            print("GDS units : ", gdsUnits)
        if 'bgnstr' in lib:
          for cell in lib['bgnstr']:
            if 'elements' in cell:
              for elem in cell['elements']:
                t = elem['type']
                if t == 'boundary':
                  layer = None
                  xmin = math.inf
                  ymin = math.inf
                  xmax = -math.inf
                  ymax = -math.inf
                  if 'layer' in elem: layer = elem['layer']
                  if layer in layerData:
                    layer = layerData[layer]
                    if 'xy' in elem:
                      for i in range(0, len(elem['xy']), 2):
                        xmin = min(xmin, elem['xy'][i] * gdsUnits)
                        xmax = max(xmax, elem['xy'][i] * gdsUnits)
                      for i in range(1, len(elem['xy']), 2):
                        ymin = min(ymin, elem['xy'][i] * gdsUnits)
                        ymax = max(ymax, elem['xy'][i] * gdsUnits)
                      if layer not in layerRects:
                        layerRects[layer] = list()
                      layerRects[layer].append(Rect(xmin, ymin, xmax, ymax))

#for l in layerRects:
#  for r in layerRects[l]:
#    print(l, r)


if (args.lef):
  pos = args.lef.find(".lef")
  outfile = args.lef[0:pos] + "_obs.lef"
  lines = []
  print("new lef file with obs : ", outfile)
  with open (args.lef, 'rt') as ifile:
    lines = ifile.readlines()
  pinRects = dict()
  with open (outfile, 'wt') as ofile:
    macroName = ""
    inMacro = False
    inPin = False
    inPort = False
    layer = ""
    inUnits = False
    inObs = False
    macroUnits = 1
    for line in lines:
      tmps = line.split()
      if tmps:
        t = tmps[0]
        if (not inMacro) and (t == "MACRO"):
          if len(tmps) > 1:
            macroName = tmps[1]
          inMacro = True
        elif inMacro and t == "UNITS":
          inUnits = True
        elif inUnits and t == "DATABASE":
          macroUnits = 1e-6 / float(tmps[3])
          print("LEF units : ", macroUnits)
        elif inMacro and t == "OBS":
          inObs = True
        elif inMacro and t == "PIN":
          inPin = True
        elif inPin and t == "PORT":
          inPort = True
        elif inPort and t == "LAYER":
          layer = tmps[1]
        elif inPort and layer and t == "RECT" and len(tmps) >= 5:
          r = Rect(float(tmps[1]) * macroUnits, float(tmps[2]) * macroUnits, float(tmps[3]) * macroUnits, float(tmps[4]) * macroUnits)
          if (layer not in pinRects):
            pinRects[layer] = []
          pinRects[layer].append(r)
        elif t == "END":
          if inUnits:
            inUnits = False
          elif inObs:
            inObs = False
          elif inPort:
            inPort = False
            layer = ""
          elif inPin:
            assert(not inPort)
            inPin = False
          elif inMacro:
            assert(not inPin and not inPort and not inUnits and not inObs)
            if pinRects and layerRects:
              ofile.write("  OBS\n")
              for l in layerRects:
                if args.use_layers and (l not in args.use_layers):
                  continue
                for r in layerRects[l]:
                  overlap = False
                  if l in pinRects:
                    for p in pinRects[l]:
                      if r.overlaps(p):
                        overlap = True
                        break
                  if not overlap:
                    tmpstr = "    LAYER " + l + " ;\n      RECT " + r.toString(macroUnits) + ' ;\n'
                    ofile.write(tmpstr)
              ofile.write("  END\n")
            inMacro = False
      ofile.write(line)
    ofile.close()

