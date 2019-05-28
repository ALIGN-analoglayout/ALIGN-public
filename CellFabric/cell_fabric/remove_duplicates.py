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


class RemoveDuplicates():

    @staticmethod
    def containedIn( s, b):
        """rS is contained in rB"""
        (rS,_) = s
        (rB,_) = b
        return rB[0] <= rS[0] and rB[1] <= rS[1] and rS[2] <= rB[2] and rS[3] <= rB[3]

#
# s touching b
# false if one rect to the left of the other
# false if one rect above the other
# true otherwise
#
    @staticmethod
    def touching( a, b):
        """a and b touch"""
        (rA,_) = a
        (rB,_) = b
        # not touching if completely to left or right or above or below
        return not (rA[2] < rB[0] or rB[2] < rA[0] or rA[3] < rB[1] or rB[3] < rA[1])

    def build_centerline_tbl( self):
        tbl = {}

        for d in self.canvas.terminals:
            layer = d['layer']
            rect = d['rect']
            netName = d['netName']

            if layer in self.skip_layers: continue

            assert layer in self.layers, layer
            twice_center = sum(rect[index]
                               for index in self.indicesTbl[self.layers[layer]][0])

            if layer not in tbl:
                tbl[layer] = {}
            if twice_center not in tbl[layer]:
                tbl[layer][twice_center] = []

            tbl[layer][twice_center].append((rect, netName))
        return tbl


    def __init__( self, canvas):
        self.canvas = canvas
        self.store_scan_lines = None
        self.shorts = []

        self.setup_layer_structures()


    def setup_layer_structures( self):
        self.layers = collections.OrderedDict()
        self.skip_layers = set()
        self.via_layers = set()

        for (nm, gen) in self.canvas.generators.items():
            if   isinstance( gen, Region):
                self.skip_layers.add( gen.layer)
                print( "Region", nm)
            elif isinstance( gen, Via):
                if gen.layer not in self.layers:
                    self.layers[gen.layer] = 'v' # Could be either --- probably want to specialize vias
                self.via_layers.add( gen.layer)
                print( "Via", nm)
            elif isinstance( gen, Wire):
                if gen.layer not in self.layers:
                    self.layers[gen.layer] = gen.direction
                print( "Wire", nm)
            else:
                assert False, (nm,type(gen))

        self.indicesTbl = {'h': ([1, 3], 0), 'v': ([0, 2], 1)}


    def build_scan_lines( self, tbl):
        self.store_scan_lines = {}

        for (layer, dir) in self.layers.items():
            if layer not in tbl: continue

            (indices, dIndex) = self.indicesTbl[dir]

            for (twice_center, v) in tbl[layer].items():

                if layer not in self.store_scan_lines: self.store_scan_lines[layer] = {}
                sl = Scanline(v[0][0], indices, dIndex)
                self.store_scan_lines[layer][twice_center] = sl

                if v:
                    (rect0, _) = v[0]
                    for (rect, netName) in v[1:]:
                        assert all(rect[i] == rect0[i] for i in indices), ("Rectangles on layer %s with the same centerline %d but different widths:" % (layer, twice_center), (indices,v))

                    s = sorted(v, key=lambda p: p[0][dIndex])

                    for (rect, netName) in s:
                        if sl.isEmpty():
                            sl.set(rect, netName)
                        elif rect[dIndex] <= sl.end:  # continue
                            sl.end = max(sl.end, rect[dIndex+2])
                            if sl.currentNet is None:
                                sl.currentNet = netName
                            elif netName is not None and sl.currentNet != netName:
                                self.shorts.append( (layer, sl.currentNet, netName))
                        else:  # gap
                            sl.emit()
                            sl.set(rect, netName)

                    if not sl.isEmpty():
                        sl.emit()
                        sl.clear()


    def check_shorts_induced_by_vias( self):
#
# Check for shorts induced by vias
# We need to do the right thing with nets named None
#

        via_layers2 = [( "via1", ("M1", "M2")), 
                       ( "via2", ("M3", "M2"))]

        for (via, (mv,mh)) in via_layers2:
            if via in self.store_scan_lines:
                for (twice_center, via_scan_line) in self.store_scan_lines[via].items():
                    metal_scan_line_vertical = self.store_scan_lines[mv][twice_center]

#
# Should scan via_scan_line and metal_scan_line_vertical simultaneously
# Easier to quadratic loop. FIX!
#

                    for via_rect in via_scan_line.rects:
                        for metal_rect in metal_scan_line_vertical.rects:
                            if self.__class__.touching( via_rect, metal_rect):
                                if via_rect[1] != metal_rect[1]:
                                    self.shorts.append( (via, via_rect, mv,  metal_rect))

                        twice_center_y = via_rect[0][1] + via_rect[0][3]
                        metal_scan_line_horizontal = self.store_scan_lines[mh][twice_center_y]

                        for metal_rect in metal_scan_line_horizontal.rects:
                            if self.__class__.touching( via_rect, metal_rect):
                                if via_rect[1] != metal_rect[1]:
                                    self.shorts.append( (via, via_rect, mh,  metal_rect))



    def generate_rectangles( self, tbl):

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

        for (layer, dir) in self.layers.items():
            if layer not in tbl: continue
            for (twice_center, v) in tbl[layer].items():
                for (rect, netName) in self.store_scan_lines[layer][twice_center].rects:
                   terminals.append( {'layer': layer, 'netName': netName, 'rect': rect})

        return terminals


    def remove_duplicates( self):

        tbl = self.build_centerline_tbl()
        self.build_scan_lines( tbl)

        self.check_shorts_induced_by_vias()

        for short in self.shorts:
            print( "SHORT", *short)

        return self.generate_rectangles( tbl)

