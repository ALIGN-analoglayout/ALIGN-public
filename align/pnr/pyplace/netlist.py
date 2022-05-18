import numpy
import gdspy
import json
import argparse
import os
import mip
import logging
import sys
import math
import pathlib

logging.basicConfig(level='ERROR')


class Point:
    def __init__(self, x = 0, y = 0):
        self._x = x
        self._y = y
    def __str__(self):
        return f'({self._x}, {self._y})'

    def transform(self, tr, w, h):
        x, y = tr._or._x + self._x, tr._or._y + self._y
        if tr._sX < 0: x -= w
        if tr._sY < 0: y -= h
        return Point(x, y)

    def moveto(self, x, y):
        self._x = x
        self._y = y

    def moveby(self, dx, dy):
        self._x += dx
        self._y += dy

class Rect:
    def __init__(self, ll = Point(math.inf, math.inf), ur = Point(-math.inf, -math.inf)):
        self._ll = ll
        self._ur = ur

    def __str__(self): return f'[{self._ll}--{self._ur}]'

    def fix(self):
        if self._ll._x > self._ur._x:
            self._ll._x, self._ur._x = self._ur._x, self._ll._x
        if self._ll._y > self._ur._y:
            self._ll._y, self._ur._y = self._ur._y, self._ll._y

    def transform(self, tr, w, h):
        ll = self._ll.transform(tr, w, h)
        ur = self._ur.transform(tr, w, h)
        r = Rect(ll, ur)
        r.fix()
        return r

    def merge(self, r):
        self._ll._x = min(self._ll._x, r._ll._x)
        self._ll._y = min(self._ll._y, r._ll._y)
        self._ur._x = max(self._ur._x, r._ur._x)
        self._ur._y = max(self._ur._y, r._ur._y)

    def xmin(self): return self._ll._x
    def ymin(self): return self._ll._y
    def xmax(self): return self._ur._x
    def ymax(self): return self._ur._y

    def width(self): return self._ur._x - self._ll._x

    def height(self): return self._ur._y - self._ll._y

    def moveby(self, dx, dy):
        self._ll.moveby(dx, dy)
        self._ur.moveby(dx, dy)

    def moveto(self, x, y):
        self._ur.moveby(x - self._ll._x, y - self._ll._y)
        self._ll.moveto(x, y)

    def overlapinx(self, r, strict = False):
        if strict:
            return self._ll._x < r._ur._x and self._ur._x > r._ll._x
        return self._ll._x <= r._ur._x and self._ur._x >= r._ll._x

    def overlapiny(self, r, strict = False):
        if strict:
            return self._ll._y < r._ur._y and self._ur._y > r._ll._y
        return self._ll._y <= r._ur._y and self._ur._y >= r._ll._y

    def overlap(self, r, strict = False):
        return self.overlapinx(r, strict) and self.overlapiny(r, strict)



class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._or = Point(oX, oY) 
        self._sX = sX
        self._sY = sY
    def __str__(self):
        return f'({self._or} {self._sX} {self._sY})'


class Constraint:
    def __init__(self, name = "", instances = list(), attr = dict()):
        self._name = name
        self._instances = instances
        self._attr = attr

class Pin:
    def __init__(self, name = "", shapes = dict()):
        self._name = name
        self._shapes = shapes
        self._bbox = Rect()
        for (h,rects) in shapes.items():
            for r in rects:
                self._bbox.merge(r)

    def addShape(self, layer, shape):
        if layer not in self._shapes:
            self._shapes[layer] = [shape]
        else:
            self._shapes[layer] = [shape]
        self._bbox.merge(shape)

    def print(self):
        print(f"    pin name : {self._name}, bbox : {self._bbox}")
        for (l, rs) in self._shapes.items():
            print(f'      layer : {l}')
            for r in rs:
                print(f"        shape : {r}")
        

class Module:
    def __init__(self, name = "", leaf = False):
        self._name      = name
        self._instances = dict()
        self._added     = False
        self._leaf      = leaf
        self._constraints = dict()
        self._pins      = set()
        self._variants  = list()
        self._placed    = False
        self._nets      = dict()

    def width(self):
        return self._bbox.width()
    def height(self):
        return self._bbox.height()

    def inorder(self, inst1, inst2):
        if "order" in self._constraints:
            for cons in self._constraints["order"]:
                if inst1 in cons._instances and inst2 in cons._instances:
                    return True
        return False

    def ishoralign(self, inst1, inst2):
        if "align" in self._constraints:
            for cons in self._constraints["align"]:
                if cons._attr["line"] in ("h_bottom", "h_top", "h_center"):
                    if inst1 in cons._instances and inst2 in cons._instances:
                        return True
        return False

    def isveralign(self, inst1, inst2):
        if "align" in self._constraints:
            for cons in self._constraints["align"]:
                if cons._attr["line"] in ("v_left", "v_right", "v_center"):
                    if inst1 in cons._instances and inst2 in cons._instances:
                        return True
        return False

    def print(self):
        print(f"module : name : {self._name}, leaf : {self._leaf}, pins : {self._pins}")
        for v in self._variants:
            v.print()
        for (name, inst) in self._instances.items():
            inst.print()
        for (name, net) in self._nets.items():
            net.print()


    def place(self):
        for (iname, inst) in self._instances.items():
            if not inst._modu._placed:
                inst._modu.place()
        print("placing module : ", self._name)
        self._placed = True



class Variant():
    def __init__(self, cname = "", modu = None, leaf = False):
        self._modu = modu
        self._name = cname
        self._bbox = Rect()
        self._pins = dict()
        self._instances = dict()

    def addPinShape(self, pinName, layer, shape):
        if pinName not in self._pins:
            self._pins[pinName] = Pin(pinName, {layer : [shape]})
        else:
            self._pins[pinName].addShape(layer, shape)

    def print(self):
        print(f'  variant name : {self._name}, bbox : {self._bbox}')
        for (name,p) in self._pins.items():
            p.print()


class Instance:
    def __init__(self, name = "", modu = None, tr = None, loc = Point(0, 0), bbox = None):
        self._name = name
        self._modu = modu
        self._tr   = tr
        self._loc  = loc
        self._bbox = bbox

    def print(self):
        print(f'  instance : {self._name}, module : {self._modu._name}, numvariants : {len(self._modu._variants)}')


class Net:
    def __init__(self, name = ""):
        self._name = name
        self._pins = list()
    def addPin(self, instName, pinName):
        self._pins.append((instName, pinName))
    def print(self):
        print(f"    net : {self._name}")
        for p in self._pins:
            print(f"      pin : {p[0]}/{p[1]}")


class Netlist:
    def __init__(self):
        self._modules = dict()

    def print(self):
        for (name,m) in self._modules.items():
            m.print()

    def loadPrimitives(self, primlist, pdir):
        primitives = dict()
        with open(primlist) as fs:
            pl = json.load(fs)
            for (pname, data) in pl.items():
                if "abstract_template_name" in data and "concrete_template_name" in data:
                    absname = data["abstract_template_name"]
                    if (data["concrete_template_name"] == pname):
                        if (absname not in primitives):
                            primitives[absname] = [data["concrete_template_name"]]
                        else:
                            primitives[absname].append(data["concrete_template_name"])
        print(f'primitives : {primitives}')

        primdir = pathlib.Path(pdir).resolve()
        if not primdir.is_dir():
            logger.error(f"Primitives directory {primdir} doesn't exist. Please enter a valid directory path")
            raise FileNotFoundError(2, 'No such primitives directory.', primdir)

        for (absname, cnames) in primitives.items():
            if absname not in self._modules:
                self._modules[absname] = Module(absname, leaf = True)
            currmodu = self._modules[absname]
            for cname in cnames:
                with (primdir / f'{cname}.json').open('rt') as fs:
                    pdata = json.load(fs)
                    currvar = Variant(cname, currmodu)
                    if "bbox" in pdata:
                        bbox = pdata["bbox"]
                        if len(bbox) == 4: currvar._bbox = Rect(Point(bbox[0], bbox[1]), Point(bbox[2], bbox[3]))
                    if "terminals" in pdata:
                        for t in pdata["terminals"]:
                            if "netName" in t and t["netName"] != None and "netType" in t and t["netType"] == "pin":
                                pinName = t["netName"]
                                currmodu._pins.add(pinName)
                                if "layer" in t and "rect" in t and len(t["rect"]) == 4:
                                    box = t["rect"]
                                    currvar.addPinShape(pinName, t["layer"], Rect(Point(box[0], box[1]), Point(box[2], box[3])))
                    currmodu._variants.append(currvar)
                                

    def loadVerilog(self, vfile):
        with open(vfile) as fp:
            pldata = json.load(fp)
            if "modules" in pldata:
                for m in pldata.get("modules"):
                    mname = m.get("name")
                    if mname:
                        if mname not in self._modules:
                            self._modules[mname] = Module(mname)
                        modu = self._modules[mname]
                        if "bbox" in m:
                            bbox = m.get("bbox")
                            modu._bbox = Rect(Point(bbox[0], bbox[1]), Point(bbox[2], bbox[3]))
                        for i in m.get("instances"):
                            iname = i.get("abstract_template_name")
                            if iname not in self._modules:
                                self._modules[iname] = Module(iname)
                            imodu = self._modules[iname]
                            instName = i.get("instance_name")
                            modu._instances[instName] = Instance(name = instName, modu = imodu)
                            for fa in i.get("fa_map"):
                                netName = fa["actual"]
                                if netName not in modu._nets:
                                    modu._nets[netName] = Net(netName)
                                modu._nets[netName].addPin(instName, fa["formal"])
                                

    def place(self):
        for (mname, m) in self._modules.items():
            if not m._placed:
                m.place()
