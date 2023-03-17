import json
import logging
import pathlib
from collections import OrderedDict
from geom import Point, Rect, Transform
import copy

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
        self._hierindex = 0 if leaf else -1

    def width(self):
        return self._bbox.width()
    def height(self):
        return self._bbox.height()

    def evalIndex(self):
        if self._leaf:
            self._hierindex = 0
            return
        index = -1
        for (iname, i) in self._instances.items():
            assert(i._modu)
            if i._modu._hierindex < 0:
                i._modu.evalIndex()
            index = max(index, i._modu._hierindex + 1)
        self._hierindex = index

    def print(self):
        print(f"module : name : {self._absname},{self._concname} hier : {self._hierindex} leaf : {self._leaf}, pins : {self._pins} bbox: {self._bbox}")
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

class HierInstance:
    def __init__(self, name = "", modu = None, tr = Transform(), loc = Point(0, 0), bbox = None):
        self._name = name
        self._modu = modu
        self._tr   = tr
        self._bbox = bbox
        self._hierinstances = list()

    def __str__(self):
        return(f'  hier instance : {self._name}, module : {self._modu._concname}, transform : {self._tr}')
    def __repr__(self):
        return(f'  hier instance : {self._name}, module : {self._modu._concname}, transform : {self._tr}')


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


class Grid:
    def __init__(self, offset = 0, pitch = 0):
        self._offset = offset
        self._pitch   = pitch

    def snap(self, x, up = True):
        if not self._pitch: return x
        rem = (x - self._offset) % self._pitch
        if rem == 0: return x
        if up: return x + (self._pitch - rem)
        return (x - rem)


class MetalLayer:
    def __init__(self, name = '', direction = 'H', width = 0, offset = 0, pitch = 0, res = 1.):
        self._name  = name
        self._grid  = Grid(offset, pitch)
        self._width = width
        self._dir   = direction
        self._res   = res
    def __str__(self):
        return f'dir : {self._dir} width : {self._width} Grid : {self._grid._offset}, {self._grid._pitch}'


class ViaLayer:
    def __init__(self, name = '', lower = None, upper = None, space = (0,0), width = (0,0), encL = (0,0), encU = (0,0), res = 1.):
        self._name = name
        self._l = lower
        self._u = upper
        self._space = space
        self._width = width
        self._encL  = encL
        self._encU  = encU
        self._res   = res
        self._viagen = None

    def addViaGen(self, width = (0, 0), space = (0, 0), num = (0, 0)):
        class ViaGen:
            def __init__(self, width, space, num):
                (self._width, self._space, self._num) = width, space, num

        self._viagen = ViaGen(width, space, num)

    def __str__(self):
        s = f'l : {self._l._name if self._l else None} u : {self._u._name if self._u else None} space : {self._space} width : {self._width} encL : {self._encL} encU : {self._encU}'
        if self._viagen:
            s += f'\n\tViaGen : width : {self._viagen._width} space : {self._viagen._space} num : {self._viagen._num}'
        return s


class Netlist:
    def __init__(self, verilog, layers, lef):
        self._modules = dict()
        self._hpitch = 0
        self._vpitch = 0
        self._mlayers = dict()
        self._vlayers = dict()
        self._flatinst = list()
        if verilog: self.loadVerilog(verilog)
        if layers: self.loadLayers(layers)
        if lef: self.loadMacros(lef)

        for (name, m) in self._modules.items():
            m.evalIndex()

    def print(self):
        for (name,m) in self._modules.items():
            m.print()
        for (name, l) in self._mlayers.items():
            print(f'layer : {name}, {l}')
        for (name, l) in self._vlayers.items():
            print(f'layer : {name}, {l}')


    def loadMacros(self, leffile):
        if leffile:
            from pnrmacro import parseLef
            macros = parseLef(leffile)
            for m in macros:
                if m._name in self._modules:
                    module = self._modules[m._name]
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
                for lD in ldata["Abstraction"]:
                    if "Layer" in lD and "Stack" not in lD:
                            if "Direction" in lD and "Offset" in lD and "Width" in lD and "Pitch" in lD:
                                self._mlayers[lD["Layer"]] = MetalLayer(lD["Layer"], lD["Direction"], lD["Width"],\
                                    lD["Offset"], lD["Pitch"], lD["UnitR"]["Mean"] if "UnitR" in lD else 1.)

                for lD in ldata["Abstraction"]:
                    if "Layer" in lD and "Stack" in lD:
                            lower = lD["Stack"][0]
                            upper = lD["Stack"][1]
                            lower = self._mlayers[lower] if lower in self._mlayers else None
                            upper = self._mlayers[upper] if upper in self._mlayers else None
                            if "SpaceX" in lD and "WidthX" in lD and "VencA_L" in lD \
                              and "VencA_H" in lD and "VencP_L" in lD and "VencP_H" in lD:
                                self._vlayers[lD["Layer"]] = ViaLayer(lD["Layer"], lower, upper, space = (lD["SpaceX"], lD["SpaceY"]), \
                                    width = (lD["WidthX"], lD["WidthY"]), encL = (lD["VencA_L"], lD["VencP_L"]), \
                                    encU = (lD["VencA_H"], lD["VencP_H"]), res = (lD["UnitR"]["Mean"] if "UnitR" in lD else 1.))
                                if "ViaCut" in lD:
                                    lV = lD["ViaCut"]
                                    if "Gen" in lV and lV["Gen"] == "ViaArrayGenerator" and "WidthX" in lV and "SpaceX" in lV and "NumX" in lV:
                                        self._vlayers[lD["Layer"]].addViaGen(width = (lV["WidthX"], lV["WidthY"]), space = (lV["SpaceX"], lV["SpaceY"]), \
                                            num = (lV["NumX"], lV["NumY"]))

    def flatten(self):
        self._flatinst = list()
        queue = list()
        topindex = -1
        for (name, m) in self._modules.items(): topindex = max(topindex, m._hierindex)

        for (name, m) in self._modules.items():
            if m._hierindex == topindex:
                hierinst = HierInstance(name = name, modu = m)
                self._flatinst.append(hierinst)
                for (iname, i) in m._instances.items():
                    hinst = HierInstance(iname, modu = i._modu)
                    hinst._tr = copy.deepcopy(i._tr)
                    hierinst._hierinstances.append(hinst)
                    queue.append(hinst)
                    self._flatinst.append(hinst)


        while len(queue):
            tmpq = list()
            for q in queue:
                for (iname, i) in q._modu._instances.items():
                    hinst = HierInstance(q._name + '/' + iname, modu = i._modu)
                    hinst._tr = copy.deepcopy(i._tr)
                    hinst._tr.apply(q._tr)
                    self._flatinst.append(hinst)
                    tmpq.append(hinst)
            queue = tmpq

        for i in self._flatinst:
            print(i._name, i._tr, i._modu._hierindex, i._modu._concname)

    def writeDEF(self):
        for (mname, m) in self._modules.items():
            if not m._leaf: m.writeDEF(mname + "_out.def")

    def writeFlatDEF(self, top = None):
        if top is not None:
            flatinstances = list()
            tmptop = None
            for f in self._flatinst:
                if top == f._name:
                    tmptop = f
                if f._name[0:len(top)] == top:
                    flatinstances.append(f)
            top = tmptop
        if top is None:
            top = self._flatinst[0] if top is None else None
            flatinstances = self._flatinst

        with open(top._modu._concname + '_flat.def', 'w') as fs:
            fs.write(f'VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN {top._modu._concname} ;\nUNITS DISTANCE MICRONS 1 ;\n')
            bbox = top._modu._bbox.transform(top._tr, top._modu.width(), top._modu.height)
            fs.write(f"DIEAREA ( {bbox._ll._x} {bbox._ll._y} ) ( {bbox._ur._x} {bbox._ur._y} ) ;\n\n")
            if len(flatinstances) > 0:
                count = 0
                for i in flatinstances:
                    if i._modu._leaf: count += 1
                fs.write(f"COMPONENTS {count} ;\n")
                for i in flatinstances:
                    if not i._modu._leaf: continue
                    x = i._tr._or._x
                    if i._tr._sX < 0: x -= i._modu.width()
                    y = i._tr._or._y
                    if i._tr._sY < 0: y -= i._modu.height()
                    fs.write(f"- {i._name} {i._modu._concname} + PLACED ( {x} {y} ) {i._tr.orient()} ;\n")
                fs.write("END COMPONENTS\n")


