#! /usr/bin/env python

import json
import sys
import math
import argparse

ap = argparse.ArgumentParser()
ap.add_argument( "-f", "--lef",   type=str, default="", help='<.lef file>')
ap.add_argument( "-r", "--rotate",   type=int, default=0, help='<angle in degrees>')
args = ap.parse_args()
print(".lef file     : ", args.lef)

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


if (args.lef):
  pos = args.lef.find(".lef")
  outfile = args.lef[0:pos] + f"_r{args.rotate}.lef"
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
    width = None
    height = None
    for line in lines:
      tmps = line.split()
      printline = True
      if tmps:
        t = tmps[0]
        if (not inMacro) and (t == "MACRO"):
          if len(tmps) > 1:
            macroName = tmps[1]
          inMacro = True
        elif inMacro and t == "SIZE":
          width = float(tmps[1]) * macroUnits
          height = float(tmps[3]) * macroUnits
          if args.rotate == 90 or args.rotate == 270:
            printline = False
            tmpstr = "  SIZE " + tmps[3] + " BY " + tmps[1] + " ;\n"
            ofile.write(tmpstr)

        elif inMacro and t == "UNITS":
          inUnits = True
        elif inUnits and t == "DATABASE":
          macroUnits = 1e-6 / float(tmps[3])
          if width:
              width *= macroUnits
              height *= macroUnits
          print("LEF units : ", macroUnits)
        elif inMacro and t == "OBS":
          inObs = True
        elif inMacro and t == "PIN":
          inPin = True
        elif inPin and t == "PORT":
          inPort = True
        elif inPort and t == "LAYER":
          layer = tmps[1]
        elif inObs and t == "LAYER":
          layer = tmps[1]
        elif (inPort or inObs) and layer and t == "RECT" and len(tmps) >= 5:
          r = Rect(float(tmps[1]) * macroUnits, float(tmps[2]) * macroUnits, float(tmps[3]) * macroUnits, float(tmps[4]) * macroUnits)
          if width and height:
            if args.rotate == 180:
              r = Rect(width - r._ur._x, height - r._ur._y, width - r._ll._x, height - r._ll._y)
            elif args.rotate == 90:
              r = Rect(height - r._ur._y, r._ll._x, height - r._ll._y, r._ur._x)
            elif args.rotate == 270:
              r = Rect(r._ll._y, width - r._ur._x, r._ur._y, width - r._ll._x)
            tmpstr = "      RECT " + r.toString(macroUnits) + ' ;\n'
            ofile.write(tmpstr)
            printline = False
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
      if printline: ofile.write(line)
    ofile.close()

