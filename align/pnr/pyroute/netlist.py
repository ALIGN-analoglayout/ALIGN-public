import json
import logging
import pathlib
from collections import OrderedDict
from geom import Point, Rect, Transform


logging.basicConfig(level='ERROR')



class Constraint:
    def __init__(self, name = "", instances = list(), attr = dict()):
        self._name = name
        self._instances = instances
        self._attr = attr

class Pin:
    def __init__(self, name = ""):
        self._name = name
        self._bbox = Rect()
        self._ports = list()

    def print(self):
        print(f"    pin name : {self._name}, bbox : {self._bbox}")

    def __repr__(self):
        s = ("name : " + str(self._name))
        for p in self._ports:
            s += ', ' + str(p)
        return s

    def __str__(self):
        s = ("name : " + str(self._name))
        for p in self._ports:
            s += ', ' + str(p)
        return s
        

class Module:
    def __init__(self, concname = "", absname = "", leaf = False):
        self._absname   = absname
        self._concname  = concname
        self._instances = dict()
        self._added     = False
        self._leaf      = leaf
        self._constraints = dict()
        self._pins      = dict()
        self._nets      = dict()
        self._obs       = None
        self._bbox      = Rect()
        self._origin    = Point(0, 0)

    def width(self):
        return self._bbox.width()
    def height(self):
        return self._bbox.height()

    def print(self):
        print(f"module : name : {self._absname},{self._concname} leaf : {self._leaf}, pins : {self._pins} bbox: {self._bbox}")
        for (name, inst) in self._instances.items():
            inst.print()
        for (name, net) in self._nets.items():
            net.print()

    def writeDEF(self, filename):
        with open(filename, 'w') as fs:
            fs.write(f'VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN {self._concname} ;\nUNITS DISTANCE MICRONS 1000 ;\n')
            fs.write(f"DIEAREA ( {self._bbox._ll._x} {self._bbox._ll._y} ) ( {self._bbox._ur._x} {self._bbox._ur._y} ) ;\n\n")
            if len(self._instances) > 0:
                fs.write(f"COMPONENTS {len(self._instances)} ;\n")
                for (iname, i) in self._instances.items():
                    x = i._tr._or._x
                    if i._tr._sX < 0: x -= i._modu.width()
                    y = i._tr._or._y
                    if i._tr._sY < 0: y -= i._modu.height()
                    fs.write(f"- {iname} {i._modu._concname} + PLACED ( {x} {y} ) {i._tr.orient()} ;\n")
                fs.write("END COMPONENTS\n")
                    


class Instance:
    def __init__(self, name = "", modu = None, tr = Transform(), loc = Point(0, 0), bbox = None):
        self._name = name
        self._modu = modu
        self._tr   = tr
        self._bbox = bbox

    def print(self):
        print(f'  instance : {self._name}, module : {self._modu._concname}, transform : {self._tr}')


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
    def __init__(self, verilog, layers, lef):
        self._modules = dict()
         #self._macros = dict()
        self._hpitch = 0
        self._vpitch = 0
        if verilog: self.loadVerilog(verilog)
        if layers: self.loadLayers(layers)
        if lef: self.loadMacros(lef)

    def print(self):
         #for (name, m) in self._macros.items():
         #    print(f'macro : {name}')
         #    m.print()
        for (name,m) in self._modules.items():
            print(f'module : {name}')
            m.print()
        print(f'vpitch : {self._vpitch} hpitch : {self._hpitch}')


    def loadMacros(self, leffile):
        if leffile:
            from pnrmacro import parseLef
            macros = parseLef(leffile)
            for (name, m) in macros.items():
                if name in self._modules:
                    module = self._modules[name]
                    module._leaf = True
                    module._origin = m._origin
                    for (pname, pin) in m._pins.items():
                        module._pins[pname] = Pin(pname)
                        for p in pin._ports:
                          module._pins[pname]._ports.append(p._lr)

                    module._obs    = m._obs
                    module._bbox   = Rect(Point(m._origin._x, m._origin._y), Point(m._origin._x + m._width, m._origin._y + m._height))

                                

    def loadVerilog(self, vfile):
        with open(vfile) as fp:
            pldata = json.load(fp)
            if "modules" in pldata:
                for m in pldata.get("modules"):
                    mname = m.get("abstract_name")
                    cname = m.get("concrete_name")
                    if cname:
                        if cname not in self._modules:
                            self._modules[cname] = Module(absname=mname, concname=cname)
                        modu = self._modules[cname]
                        if "bbox" in m:
                            bbox = m.get("bbox")
                            modu._bbox = Rect(Point(bbox[0], bbox[1]), Point(bbox[2], bbox[3]))
                        for i in m.get("instances"):
                            imname = i.get("abstract_template_name")
                            icname = i.get("concrete_template_name")
                            if icname not in self._modules:
                                self._modules[icname] = Module(absname=imname, concname=icname)
                            imodu = self._modules[icname]
                            instName = i.get("instance_name")
                            modu._instances[instName] = Instance(name = instName, modu = imodu)
                            for fa in i.get("fa_map"):
                                netName = fa["actual"]
                                if netName not in modu._nets:
                                    modu._nets[netName] = Net(netName)
                                modu._nets[netName].addPin(instName, fa["formal"])
                            if "transformation" in i:
                                tr = i.get("transformation")
                                modu._instances[instName]._tr = Transform(tr["oX"], tr["oY"], tr["sX"], tr["sY"])
                    if "parameters" in m:
                        for p in m["parameters"]: modu._pins[p] = None

    def loadLayers(self, layersfile):
        with open(layersfile) as fp:
            ldata = json.load(fp, object_pairs_hook=OrderedDict)
            if "Abstraction" in ldata:
                for layerData in ldata["Abstraction"]:
                    if "Layer" in layerData and layerData["Layer"][0] == "M":
                        if "Direction" in layerData:
                            if layerData["Direction"] == "V" and self._vpitch <= 0:
                                self._vpitch = layerData["Pitch"]
                            if layerData["Direction"] == "H" and self._hpitch <= 0:
                                self._hpitch = layerData["Pitch"]
                    if self._vpitch > 0 and self._hpitch > 0 : break


    def writeDEF(self):
        for (mname, m) in self._modules.items():
            if not m._leaf: m.writeDEF(mname + "_out.def")
