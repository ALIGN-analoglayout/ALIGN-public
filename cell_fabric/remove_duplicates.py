import collections

from .generators import *

class Scanline:
    def __init__(self, proto, indices, dIndex):
        self.proto = proto
        self.indices = indices
        self.dIndex = dIndex
        self.rects = []
        self.clear()

    def clear(self):
        self.start = None
        self.end = None
        self.currentNet = None

    def isEmpty(self):
        return self.start is None

    def emit(self):
        r = self.proto[:]
        r[self.dIndex] = self.start
        r[self.dIndex+2] = self.end
        self.rects.append((r, self.currentNet))

    def set(self, rect, netName):
        self.start = rect[self.dIndex]
        self.end = rect[self.dIndex+2]
        self.currentNet = netName

def remove_duplicates( canvas):
    layers = collections.OrderedDict()
    skip_layers = set()

    for (nm, gen) in canvas.generators.items():
        if   isinstance( gen, Region):
            skip_layers.add( gen.layer)
            print( "Region", nm)
        elif isinstance( gen, Via):
            if gen.layer not in layers:
                layers[gen.layer] = 'v' # Don't want to do this
            print( "Via", nm)
        elif isinstance( gen, Wire):
            if gen.layer not in layers:
                layers[gen.layer] = gen.direction
            print( "Wire", nm)
        else:
            assert False, (nm,type(gen))

    hLayers = {layer for (layer, dir) in layers.items() if dir == 'h'}
    vLayers = {layer for (layer, dir) in layers.items() if dir == 'v'}

    indicesTbl = {'h': ([1, 3], 0), 'v': ([0, 2], 1)}

    tbl = {}

    terminals = []

    for d in canvas.terminals:
        layer = d['layer']
        rect = d['rect']
        netName = d['netName']

        if layer in skip_layers:
            terminals.append( d)
            continue

        assert layer in layers, layer
        twice_center = sum(rect[index]
                           for index in indicesTbl[layers[layer]][0])

        if layer not in tbl:
            tbl[layer] = {}
        if twice_center not in tbl[layer]:
            tbl[layer][twice_center] = []

        tbl[layer][twice_center].append((rect, netName))



    for (layer, dir) in layers.items():
        if layer not in tbl:
            continue
        (indices, dIndex) = indicesTbl[dir]

        for (twice_center, v) in tbl[layer].items():

            sl = Scanline(v[0][0], indices, dIndex)

            if v:
                (rect0, _) = v[0]
                for (rect, netName) in v[1:]:
                    assert all(rect[i] == rect0[i] for i in indices)

                s = sorted(v, key=lambda p: p[0][dIndex])

                for (rect, netName) in s:
                    if sl.isEmpty():
                        sl.set(rect, netName)
                    elif rect[dIndex] <= sl.end:  # continue
                        sl.end = max(sl.end, rect[dIndex+2])
                        assert sl.currentNet == netName, (
                            layer, sl.currentNet, netName)
                    else:  # gap
                        sl.emit()
                        sl.set(rect, netName)

                if not sl.isEmpty():
                    sl.emit()
                    sl.clear()

            for (rect, netName) in sl.rects:
                terminals.append(
                    {'layer': layer, 'netName': netName, 'rect': rect})

    return terminals
