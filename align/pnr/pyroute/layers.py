from geom import Point, Rect
import json
from collections import OrderedDict

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

    def getPointsInRange(self, xmin, xmax):
        x = self.snap(xmin, up = True)
        pts = []
        while x <= xmax:
            pts.append(x)
            x += self._pitch
        return pts


class MetalLayer:
    def __init__(self, name = '', direction = 'H', width = 0, offset = 0, pitch = 0, res = 1.):
        self._name  = name
        self._grid  = Grid(offset, pitch)
        self._width = width
        self._dir   = direction
        self._res   = res
        self._index = -1
    def __str__(self):
        return f'name : {self._name} dir : {self._dir} width : {self._width} Grid : {self._grid._offset}, {self._grid._pitch}'


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
        self._via  = dict()

    def addViaGen(self, width = (0, 0), space = (0, 0), num = (0, 0)):
        class ViaGen:
            def __init__(self, width, space, num):
                (self._width, self._space, self._num) = width, space, num

        self._viagen = ViaGen(width, space, num)

    def __str__(self):
        s = f'name : {self._name} l : {self._l._name if self._l else None} u : {self._u._name if self._u else None} space : {self._space} width : {self._width} encL : {self._encL} encU : {self._encU}'
        if self._viagen:
            s += f'\n\tViaGen : width : {self._viagen._width} space : {self._viagen._space} num : {self._viagen._num}'
        return s

    def buildVia(self):
        if self._u and self._l:
            encL = self._encL if self._l._dir == 'H' else (self._encL[1], self._encL[0])
            encU = self._encU if self._u._dir == 'H' else (self._encU[1], self._encU[0])
            if not self._viagen:
                self._via[self._name] = [Rect(Point(-self._width[0]/2, -self._width[1]/2), Point(self._width[0]/2, self._width[1]/2))]
                self._via[self._l._name] = [Rect(Point(-self._width[0]/2 - encL[0], -self._width[1]/2 - encL[1]), Point(self._width[0]/2 + encL[0], self._width[1]/2 + encL[1]))]
                self._via[self._u._name] = [Rect(Point(-self._width[0]/2 - encU[0], -self._width[1]/2 - encU[1]), Point(self._width[0]/2 + encU[0], self._width[1]/2 + encU[1]))]
            else:
                width = (self._viagen._width[0] * self._viagen._num[0] + self._viagen._space[0] * (self._viagen._num[0] - 1), \
                         self._viagen._width[1] * self._viagen._num[1] + self._viagen._space[1] * (self._viagen._num[1] - 1))
                self._via[self._name] = []
                for i in range(self._viagen._num[0]):
                    for j in range(self._viagen._num[1]):
                        x = -width[0]/2 + i * (self._viagen._width[0] + self._viagen._space[0])
                        y = -width[1]/2 + j * (self._viagen._width[1] + self._viagen._space[1])
                        self._via[self._name].append(Rect(Point(x, y), Point(x + self._viagen._width[0], y + self._viagen._width[1])))
                self._via[self._l._name] = [Rect(Point(-width[0]/2 - encL[0], -width[1]/2 - encL[1]), Point(width[0]/2 + encL[0], width[1]/2 + encL[1]))]
                self._via[self._u._name] = [Rect(Point(-width[0]/2 - encU[0], -width[1]/2 - encU[1]), Point(width[0]/2 + encU[0], width[1]/2 + encU[1]))]

class Layers:
    def __init__(self, layersfile = ''):
        self._mlayers = dict()
        self._vlayers = dict()
        self._minlayer = ''
        self._maxlayer = ''
        self._mlarray = list()
        self._vlarray = dict()


        if layersfile:
            self.loadLayers(layersfile)

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
            if "design_info" in ldata and "top_signal_routing_layer" in ldata["design_info"] and "bottom_signal_routing_layer" in ldata["design_info"]:
                self._maxlayer = ldata["design_info"]["top_signal_routing_layer"]
                self._minlayer = ldata["design_info"]["bottom_signal_routing_layer"]
        for (l, v) in self._vlayers.items():
            v.buildVia()

        for (l, m) in self._mlayers.items():
            if l[0] == 'M':
                layer = int(l[1:]) - 1
                if layer >= len(self._mlarray):
                    n = layer + 1 - len(self._mlarray)
                    self._mlarray.extend([None for i in range(n)])
                self._mlarray[layer] = m
                m._index = layer
        for (l, v) in self._vlayers.items():
            if v._l and v._u and v._l._name[0] == 'M' and v._u._name[0] == 'M':
                self._vlarray[(int(v._l._name[1:]) - 1, int(v._u._name[1:]) - 1)] = v

        if self._minlayer and self._maxlayer:
            self._minlayer = self._mlayers[self._minlayer]
            self._maxlayer = self._mlayers[self._maxlayer]

    def print(self):
        for index in range(len(self._mlarray)):
            print(f'layer : {index}, {self._mlarray[index]}')
        for (index, l) in self._vlarray.items():
            print(f'layer : {index}, {l}')


