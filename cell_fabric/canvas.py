from . import transformation
import copy
import collections


class Wire:
    def __init__( self, nm, layer, direction, *, clg, spg):
        self.nm = nm
        self.layer = layer
        self.direction = direction
        assert direction in ['v','h']
        self.clg = clg
        self.spg = spg

    def segment( self, netName, pinName, center, bIdx, eIdx, *, bS=None, eS=None):
        if bS is None: bS=self.spg
        if eS is None: eS=self.spg

        (c,(w,clr)) = self.clg.value( center)
        c0 = c - w//2
        c1 = c + w//2
        bPhys = bS.value(bIdx)[0]
        ePhys = eS.value(eIdx)[0]
        if self.direction == 'h':
            rect = [ bPhys, c0, ePhys, c1]
        else:
            rect = [ c0, bPhys, c1, ePhys]
        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        if clr is not None:
            data['color'] = clr

        return data

class Region:
    def __init__( self, nm, layer, *, h_grid, v_grid):
        self.nm = nm
        self.layer = layer
        self.h_grid = h_grid
        self.v_grid = v_grid

    def physical_x( self, grid_x):
        return self.v_grid.value( grid_x)[0]

    def physical_y( self, grid_y):
        return self.h_grid.value( grid_y)[0]

    def segment( self, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1):

        rect = [self.physical_x(grid_x0), self.physical_y(grid_y0),
                self.physical_x(grid_x1), self.physical_y(grid_y1)]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        return data

class Via:
    def __init__( self, nm, layer, *, h_clg, v_clg):
        self.nm = nm
        self.layer = layer           

        self.h_clg = h_clg
        self.v_clg = v_clg

    def physical_xs( self, p):
        (c,(w,_)) = self.v_clg.value( p)
        return (c-w//2,c+w//2)

    def physical_ys( self, p):
        (c,(w,_)) = self.h_clg.value( p)
        return (c-w//2,c+w//2)

    def segment( self, netName, pinName, grid_cx, grid_cy):
        (x0,x1) = self.physical_xs( grid_cx)
        (y0,y1) = self.physical_ys( grid_cy)
        rect = [ x0, y0, x1, y1]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        return data


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


class Canvas:
    def computeBbox( self):
        self.bbox = transformation.Rect(None,None,None,None)
        for term in self.terminals:
            r = transformation.Rect( *term['rect'])
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

    def addGen( self, gen):
        assert gen.nm not in self.generators
        self.generators[gen.nm] = gen
        return gen
 
    def addWire( self, grid, netName, pinName, c, bIdx, eIdx, *, bS=None, eS=None):
        segment = grid.segment( netName, pinName, c, bIdx, eIdx, bS=bS, eS=eS)
        self.terminals.append( segment)
        return segment
       
    def addRegion( self, grid, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1):
        segment = grid.segment( netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1)
        self.terminals.append( segment)
        return segment

    def addVia( self, grid, netName, pinName, cx, cy):
        segment = grid.segment( netName, pinName, cx, cy)
        self.terminals.append( segment)
        return segment


    def __init__( self):
        self.terminals = []
        self.generators = collections.OrderedDict()

    def removeDuplicates( self):

        layers = collections.OrderedDict()
        skip_layers = set()

        for (nm, gen) in self.generators.items():
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

        for d in self.terminals:
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
