import json
import logging
from geom import Point, Rect, Transform
import copy
from layers import Layers

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
        for (iname, inst) in self._instances.items():
            assert(inst._modu)
            if inst._modu._hierindex < 0:
                inst._modu.evalIndex()
            index = max(index, inst._modu._hierindex + 1)
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
                for (iname, inst) in self._instances.items():
                    x = inst._tr._or._x
                    if inst._tr._sX < 0: x -= inst._modu.width()
                    y = inst._tr._or._y
                    if inst._tr._sY < 0: y -= inst._modu.height()
                    fs.write(f"- {iname} {inst._modu._concname} + PLACED ( {x} {y} ) {inst._tr.orient()} ;\n")
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
    def __init__(self, name = "", mname = "", modu = None, tr = Transform(), loc = Point(0, 0), bbox = None):
        self._name = name
        self._mastername = mname
        self._modu = modu
        self._tr   = tr
        self._bbox = bbox
        self._hierinstances = dict()
        self._nets = dict()
        self._pins = dict()
        self._routed = False
        self._obs = None

    def __str__(self):
        return(f'(hier instance : {self._name}, module : {self._modu._concname}, transform : {self._tr})')
    def __repr__(self):
        return(f'(hier instance : {self._name}, module : {self._modu._concname}, transform : {self._tr})')

    def route(self):
        if len(self._hierinstances) == 0:
            self._routed = True
            return
        for child in self._hierinstances.values():
            if not child._routed:
                child.route()
        print(f"routing hier : {self._name}")
        self._routed = True

    def writeLEF(self):
        with open(self._name + "_out.lef", 'w') as fs:
            fs.write(f'MACRO {self._name}\n   ORIGIN 0 0 ;\n')
            if len(self._pins):
                for (pname, pin) in self._pins.items():
                    fs.write(f"   PIN {pname}\n      DIRECTION INOUT ;\n      USE SIGNAL ;\n")
                    for port in pin._ports:
                        fs.write("         PORT\n")
                        for (l, rects) in port.items():
                            fs.write(f"            LAYER {l} ;\n")
                            for r in rects:
                                fs.write(f"            RECT {r._ll._x} {r._ll._y} {r._ur._x} {r._ur._y} ;\n")
                        fs.write("         END\n")
                    fs.write(f"   END {pname}\n")

            if len(self._obs):
                fs.write("   OBS\n")
                for (l, rects) in self._obs.items():
                    fs.write(f"      LAYER {l} ;\n")
                    for r in rects:
                        fs.write(f"         RECT {r._ll._x} {r._ll._y} {r._ur._x} {r._ur._y} ;\n")
                fs.write("   END\n")
            fs.write(f'END {self._name}\n')



class Net:
    def __init__(self, name = ""):
        self._name = name
        self._pins = list()
        self._shapes = dict()
    def addPin(self, instName, pinName):
        self._pins.append((instName, pinName))
    def print(self):
        print(f"    net : {self._name}")
        for p in self._pins:
            print(f"      pin : {p[0]}/{p[1]}")


class Netlist:
    def __init__(self, verilog, layers, lef):
        self._modules = dict()
        self._hpitch = 0
        self._vpitch = 0
        self._flatinst = list()
        self._layers = Layers(layers)
        if verilog: self.loadVerilog(verilog)
        if lef: self.loadMacros(lef)
        self._maxhier = -1

        for (name, m) in self._modules.items():
            m.evalIndex()
        self.flatten()

    def print(self):
        for (name,m) in self._modules.items():
            m.print()
        self._layers.print()


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

                    module._obs = dict()
                    for (l, obs) in m._obs.items():
                        if l not in module._obs:
                            module._obs[l] = copy.deepcopy(obs)
                        else:
                            module._obs[obs._layer].extend(obs)
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
                        for inst in m.get("instances"):
                            imname = inst.get("abstract_template_name")
                            icname = inst.get("concrete_template_name")
                            if icname not in self._modules:
                                self._modules[icname] = Module(absname=imname, concname=icname)
                            imodu = self._modules[icname]
                            instName = inst.get("instance_name")
                            modu._instances[instName] = Instance(name = instName, modu = imodu)
                            for fa in inst.get("fa_map"):
                                netName = fa["actual"]
                                if netName not in modu._nets:
                                    modu._nets[netName] = Net(netName)
                                modu._nets[netName].addPin(instName, fa["formal"])
                            if "transformation" in inst:
                                tr = inst.get("transformation")
                                modu._instances[instName]._tr = Transform(tr["oX"], tr["oY"], tr["sX"], tr["sY"])
                    if "parameters" in m:
                        for p in m["parameters"]: modu._pins[p] = Pin(p)

    def flatten(self):
        self._flatinst = list()
        queue = list()
        self._maxhier = -1
        for (name, m) in self._modules.items(): self._maxhier = max(self._maxhier, m._hierindex)

        for (name, m) in self._modules.items():
            if m._hierindex == self._maxhier:
                hierinst = HierInstance(name = name, mname = name, modu = m)
                self._flatinst.append(hierinst)
                for (iname, inst) in m._instances.items():
                    hinst = HierInstance(iname, mname = iname, modu = inst._modu)
                    hinst._tr = copy.deepcopy(inst._tr)
                    hierinst._hierinstances[iname] = hinst
                    queue.append(hinst)
                    self._flatinst.append(hinst)


        while len(queue):
            tmpq = list()
            for q in queue:
                for (iname, inst) in q._modu._instances.items():
                    hinst = HierInstance(q._name + '/' + iname, mname = iname, modu = inst._modu)
                    hinst._tr = copy.deepcopy(inst._tr)
                    hinst._tr.apply(q._tr)
                    self._flatinst.append(hinst)
                    q._hierinstances[iname] = hinst
                    tmpq.append(hinst)
            queue = tmpq

         #for inst in self._flatinst:
         #    print(inst._name, inst._tr, inst._modu._hierindex, inst._modu._concname)

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
                for inst in flatinstances:
                    if inst._modu._leaf: count += 1
                fs.write(f"COMPONENTS {count} ;\n")
                for inst in flatinstances:
                    if not inst._modu._leaf: continue
                    x = inst._tr._or._x
                    if inst._tr._sX < 0: x -= inst._modu.width()
                    y = inst._tr._or._y
                    if inst._tr._sY < 0: y -= inst._modu.height()
                    fs.write(f"- {inst._name} {inst._modu._concname} + PLACED ( {x} {y} ) {inst._tr.orient()} ;\n")
                fs.write("END COMPONENTS\n")

    def route(self):
        routeHierOrder = [[] for i in range(self._maxhier + 1)]
        for inst in self._flatinst:
            if inst._modu._hierindex >= 0: routeHierOrder[inst._modu._hierindex].append(inst)
        for inst in routeHierOrder[0]:
            inst._obs = copy.deepcopy(inst._modu._obs)
            for (l, rects) in inst._obs.items():
                for i in range(len(rects)):
                    rects[i] = rects[i].transform(inst._tr, inst._modu.width(), inst._modu.height())
            inst._pins = copy.deepcopy(inst._modu._pins)
            for (pname, pin) in inst._pins.items():
                for port in pin._ports:
                    for (l, rects) in port.items():
                        for i in range(len(rects)):
                            rects[i] = rects[i].transform(inst._tr, inst._modu.width(), inst._modu.height())
        for i in range(1, len(routeHierOrder)):
            if len(routeHierOrder[i]): print("hier : ", i, routeHierOrder[i])
            for hierinst in routeHierOrder[i]:
                for child in hierinst._hierinstances.values():
                    if not hierinst._obs: hierinst._obs = dict()
                    for (l, rects) in child._obs.items():
                        if l not in hierinst._obs:
                            hierinst._obs[l] = list()
                        for r in rects:
                            hierinst._obs[l].append(r)
                for (nname, net) in hierinst._modu._nets.items():
                    newnet = Net(nname)
                    for (instname, pin) in net._pins:
                        for port in hierinst._hierinstances[instname]._pins[pin]._ports:
                            for (layer, rects) in port.items():
                                if layer not in newnet._shapes: newnet._shapes[layer] = list()
                                newnet._shapes[layer].extend(rects)
                    hierinst._nets[nname] = newnet

                for (pname, pin) in hierinst._modu._pins.items():
                    if pname in hierinst._nets:
                        pin = Pin(pname)
                        pin._ports.append(hierinst._nets[pname]._shapes)
                        hierinst._pins[pname] = pin
                        

                hierinst.route()
                hierinst.writeLEF()
