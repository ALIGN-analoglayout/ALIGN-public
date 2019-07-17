
from collections import defaultdict, OrderedDict

from .generators import *

class UnionFind:
    def __init__(self):
        self.dad = self

    def root( self):
        root = self
        while root.dad != root:
            root = root.dad

        # Path compression
        x = self
        while x.dad != x:
            x.dad,x = root,x.dad

        return root

    def connect( self, other):
        other.root().dad = self.root()
    
class ScanlineRect(UnionFind):
    def __init__(self):
        super().__init__()
        self.rect = None
        self.netName = None
        self.isPorted = False

    def __repr__(self):
        return str( (self.rect, self.netName))

class Scanline:
    def __init__(self, proto, indices, dIndex):
        self.proto = proto
        self.indices = indices
        self.dIndex = dIndex
        self.rects = []
        self.clear()
        self.dad = None

    def clear(self):
        self.start = None
        self.end = None
        self.currentNet = None
        self.currentIsPorted = False

    def isEmpty(self):
        return self.start is None

    def emit(self):
        r = self.proto[:]
        r[self.dIndex] = self.start
        r[self.dIndex+2] = self.end
        slr = ScanlineRect()
        slr.rect = r
        slr.netName = self.currentNet
        slr.isPorted = self.isPorted
        self.rects.append(slr)

    def set_named_rect(self, rect, netName, *, isPorted=False):
        self.start = rect[self.dIndex]
        self.end = rect[self.dIndex+2]
        self.currentNet = netName
        self.isPorted = isPorted

    def __repr__( self):
        return 'Scanline( rects=' + str(self.rects) + ')'

    def find_touching(self, via_rect):
#
# Linear search --- could improve performance by binary search since rects are sorted
#
        result = None
        for metal_rect in self.rects:
            if RemoveDuplicates.touching( via_rect.rect, metal_rect.rect):
                result = metal_rect
                break

        assert result is not None
        return result

class RemoveDuplicates():

    def dump(self):
        tbl = defaultdict(lst)

        for (layer,v) in self.store_scan_lines.items():
            for vv in v.values():
                for slr in vv.rects:
                    tbl[id(slr.root())].append( (slr,root.netName,layer))

        for (i,s) in tbl.items():
            print( "Equivalence classes:", i, s)

    def check_opens(self):
        self.opens = []

        tbl = defaultdict(lambda: defaultdict(list))

        for (layer,v) in self.store_scan_lines.items():
            for vv in v.values():
                for slr in vv.rects:
                    root = slr.root()
                    nm = root.netName
                    if nm is not None:
                        tbl[nm][id(root)].append( (layer, slr.rect))

        for (nm,s) in tbl.items():
            if len(s) > 1:
                self.opens.append( (nm,list(s.values())))


    @staticmethod
    def containedIn( rS, rB):
        """rS is contained in rB"""
        return rB[0] <= rS[0] and rB[1] <= rS[1] and rS[2] <= rB[2] and rS[3] <= rB[3]

    @staticmethod
    def touching( rA, rB):
        """rA and rB touch"""
        # not touching if completely to left or right or above or below
        return not (rA[2] < rB[0] or rB[2] < rA[0] or rA[3] < rB[1] or rB[3] < rA[1])

    def __init__( self, canvas):
        self.canvas = canvas
        self.store_scan_lines = None
        self.shorts = []

        self.setup_layer_structures()


    def setup_layer_structures( self):
        self.layers = OrderedDict()
        self.skip_layers = set()
        self.via_layers = set()

        for (nm, gen) in self.canvas.generators.items():
            if   isinstance( gen, Region):
                self.skip_layers.add( gen.layer)
            elif isinstance( gen, Via):
                if gen.layer not in self.layers:
                    self.layers[gen.layer] = '*' # Specialize for vias
                self.via_layers.add( gen.layer)
            elif isinstance( gen, Wire):
                if gen.layer not in self.layers:
                    self.layers[gen.layer] = gen.direction
            else:
                assert False, (nm,type(gen))

        self.indicesTbl = {'h': ([1, 3], 0), 'v': ([0, 2], 1), '*': ([0, 2], 1)}


    def build_centerline_tbl( self):
        tbl = defaultdict(lambda: defaultdict(list))

        for d in self.canvas.terminals:
            layer = d['layer']
            rect = d['rect']
            netName = d['netName']
            isPorted = 'pin' in d
            if isPorted:
                assert netName == d['pin'], f"{netName} does not match {d['pin']}"

            if layer in self.skip_layers: continue

            assert layer in self.layers, layer
            twice_center = sum(rect[index]
                               for index in self.indicesTbl[self.layers[layer]][0])

            tbl[layer][twice_center].append((rect, netName, isPorted))
        return tbl


    def build_scan_lines( self, tbl):
        self.store_scan_lines = defaultdict(dict)

        for (layer, dir) in self.layers.items():
            if layer not in tbl: continue

            (indices, dIndex) = self.indicesTbl[dir]

            for (twice_center, v) in tbl[layer].items():

                (rect0, _, _) = v[0]
                for (rect, _, _) in v[1:]:
                    assert all(rect[i] == rect0[i] for i in indices), ("Rectangles on layer %s with the same centerline %d but different widths:" % (layer, twice_center), (indices,v))

                sl = self.store_scan_lines[layer][twice_center] = Scanline(v[0][0], indices, dIndex)

                for (rect, netName, isPorted) in sorted(v, key=lambda p: p[0][dIndex]):
                    if sl.isEmpty():
                        sl.set_named_rect(rect, netName, isPorted=isPorted)
                    elif rect[dIndex] <= sl.end:  # continue
                        sl.end = max(sl.end, rect[dIndex+2])
                        if sl.currentNet is None:
                            sl.currentNet = netName
                            sl.currentIsPorted = isPorted
                        elif netName is not None and sl.currentNet != netName:
                            self.shorts.append( (layer, sl.currentNet, netName))
                    else:  # gap
                        sl.emit()
                        sl.set_named_rect(rect, netName, isPorted=isPorted)

                if not sl.isEmpty():
                    sl.emit()
                    sl.clear()


    def check_shorts_induced_by_vias( self):

        connections = []

        for (via, (mv,mh)) in self.canvas.layer_stack:
            if via in self.store_scan_lines:
                for (twice_center, via_scan_line) in self.store_scan_lines[via].items():
                    metal_scan_line_vertical = self.store_scan_lines[mv][twice_center]
                    for via_rect in via_scan_line.rects:
                        metal_rect_v = metal_scan_line_vertical.find_touching(via_rect)
                        twice_center_y = via_rect.rect[1] + via_rect.rect[3]
                        metal_scan_line_horizontal = self.store_scan_lines[mh][twice_center_y]
                        metal_rect_h = metal_scan_line_horizontal.find_touching(via_rect)
                        connections.append( (via_rect, metal_rect_v, metal_rect_h))
                        
        def connectPair( a, b):
            def aux( a, b):
                if a.netName is None:
                    b.connect( a)
                elif b.netName is None or a.netName == b.netName:
                    a.connect( b)
            aux( a.root(), b.root())

        for triple  in connections:
            connectPair( triple[1], triple[2])
            connectPair( triple[0], triple[1])

            nms = { root.netName for slr in list(triple) for root in [slr.root()] if root.netName is not None}

            if len(nms) > 1:
                self.shorts.append( triple)

    def generate_rectangles( self):

        terminals = []
#
# Write out regions
#
        for d in self.canvas.terminals:
            if d['layer'] in self.skip_layers:
                terminals.append( d)

#
# Write out the rectangles stored in the scan line data structure
#
        for (layer,vv) in self.store_scan_lines.items():
            for (twice_center, v) in vv.items():
                for slr in v.rects:
                    root = slr.root()
                    terminals.append( {'layer': layer, 'netName': root.netName, 'rect': slr.rect})
                    if slr.isPorted:
                        terminals[-1]['pin'] = root.netName

        return terminals


    def remove_duplicates( self):

        self.build_scan_lines( self.build_centerline_tbl())

        self.check_shorts_induced_by_vias()
        self.check_opens()

        for short in self.shorts:
            print( "SHORT", *short)
        for opn in self.opens:
            print( "OPEN", *opn)

        return self.generate_rectangles()

