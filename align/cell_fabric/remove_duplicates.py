
from collections import defaultdict, OrderedDict
import pprint

from .generators import *

import logging
logger = logging.getLogger(__name__)

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
        self.netType = None
        self.terminal = None
        self.isPorted = False

    def __repr__(self):
        return str( (self.rect, self.netName, self.netType))

class Scanline:
    def __init__(self, indices, dIndex):
        self.indices = indices
        self.dIndex = dIndex
        self.rects = []
        self.dad = None

    def isEmpty(self):
        return len(self.rects) == 0

    @staticmethod
    def new_slr_no_add( rect, netName, netType, *, isPorted=False):
        slr = ScanlineRect()
        slr.rect = rect[:]
        slr.netType = netType
        if netName is not None and ':' in netName:
            slr.terminal = tuple(netName.split(':'))
            assert len(slr.terminal) == 2
        else:
            slr.netName = netName
        slr.isPorted = isPorted
        return slr

    def add_slr(self, slr):
        self.rects.append(slr)
        return slr

    def new_slr(self, rect, netName, netType, *, isPorted=False):
        self.add_slr( self.new_slr_no_add( rect, netName, netType, isPorted=isPorted))
        return slr

    def merge_slr(self, base_slr, new_slr):
        base_slr.rect[self.dIndex+2] = max(base_slr.rect[self.dIndex+2], new_slr.rect[self.dIndex+2])        
        base_slr.isPorted = base_slr.isPorted or new_slr.isPorted

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

        assert result is not None, (via_rect, self.rects)
        return result

class RemoveDuplicates():

    def dump(self):
        tbl = defaultdict(lst)

        for (layer,v) in self.store_scan_lines.items():
            #print(v)
            for vv in v.values():
                for slr in vv.rects:
                    tbl[id(slr.root())].append( (slr,root.netName,layer))

        for (i,s) in tbl.items():
            logger.debug( pprint.pformat(["Equivalence classes:", i, s]))

    def check_opens(self):

        tbl = defaultdict(lambda: defaultdict(list))

        for (layer,v) in self.store_scan_lines.items():
            for vv in v.values():
                for slr in vv.rects:
                    root = slr.root()
                    nm = root.netName
                    if nm is not None:
                        tbl[nm][id(root)].append( (layer, slr.rect))
                    elif slr.terminal is not None:
                        self.subinsts[slr.terminal[0]].pins[slr.terminal[1]].add( None)
                        self.set_open( slr.terminal, slr.terminal)

        for (nm,s) in tbl.items():
            if len(s) > 1:
                self.set_open( nm, (nm,list(s.values())))


    @staticmethod
    def containedIn( rS, rB):
        """rS is contained in rB"""
        return rB[0] <= rS[0] and rB[1] <= rS[1] and rS[2] <= rB[2] and rS[3] <= rB[3]

    @staticmethod
    def touching( rA, rB):
        """rA and rB touch"""
        # not touching if completely to left or right or above or below
        return not (rA[2] < rB[0] or rB[2] < rA[0] or rA[3] < rB[1] or rB[3] < rA[1])

    def __init__( self, canvas, *, nets_allowed_to_be_open=None, allow_opens=False):
        self.canvas = canvas
        self.store_scan_lines = None
        self.different_widths = []
        self.shorts = []
        self.opens = []
        self.subinsts = canvas.subinsts

        self.setup_layer_structures()

        if nets_allowed_to_be_open is None:
            self.nets_allowed_to_be_open = set([])
        else:
            self.nets_allowed_to_be_open = set(nets_allowed_to_be_open)
        self.allow_opens = bool(allow_opens)

    def set_open( self, nm, opn):
        if nm not in self.nets_allowed_to_be_open and not self.allow_opens:
            self.opens.append( opn)

    def setup_layer_structures( self):
        self.layers = OrderedDict()
        self.skip_layers = set()
        self.via_layers = set()

        # Should use a region generator
        self.skip_layers.add( 'boundary')
        self.skip_layers.add( 'Rboundary')

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
            netType = d['netType']
            isPorted = 'pin' in d
            if isPorted:
                assert netName == d['pin'], f"{netName} does not match {d['pin']}"
            if layer in self.skip_layers: continue
            if layer in self.layers:
                twice_center = sum(rect[index]
                                   for index in self.indicesTbl[self.layers[layer]][0])
                tbl[layer][twice_center].append((rect, netName, netType, isPorted))
            else:
                logger.warning( f"Layer {layer} not in {self.layers}")

        return tbl


    def build_scan_lines( self, tbl):
        skip_layers_for_different_widths = ['Active']

        self.store_scan_lines = defaultdict(dict)

        for (layer, dir) in self.layers.items():
            if layer not in tbl: continue

            (indices, dIndex) = self.indicesTbl[dir]

            for (twice_center, v) in tbl[layer].items():

                different_widths_in_bin = False

                (rect0, _, _, _) = v[0]
                for (rect, _, _, _) in v[1:]:
                    if not all(rect[i] == rect0[i] for i in indices):
                        widths = set()
                        for (r, _, _, _) in v:
                            widths.add( r[indices[1]]-r[indices[0]])
                        if layer not in skip_layers_for_different_widths:
                            different_widths_in_bin = True
                            tup = (f"Rectangles on layer {layer} with the same 2x centerline {twice_center} but different widths {widths}:", (indices,v))
                            #logger.warning( f"{tup}")
                            self.different_widths.append( tup)

                sl = self.store_scan_lines[layer][twice_center] = Scanline( indices, dIndex)

                current_slr = None
                for (rect, netName, netType, isPorted) in sorted(v, key=lambda p: p[0][dIndex]):
                    potential_slr = sl.new_slr_no_add(rect, netName, netType, isPorted=isPorted)
                    if not sl.isEmpty() and \
                        rect[dIndex] <= current_slr.rect[dIndex+2] and \
                        all(rect[i] == current_slr.rect[i] for i in indices):  # continuation
                        if self.connectPair(layer,current_slr, potential_slr):
                            if (potential_slr.netType not in ['blockage'] and current_slr.netType not in ['blockage']):
                                sl.merge_slr(current_slr, potential_slr)
                            else:
                                current_slr = sl.add_slr( potential_slr)
                        else:
                            current_slr = sl.add_slr( potential_slr)
                    else:  # empty or gap or different width
                        current_slr = sl.add_slr( potential_slr)

                    # invariant (can probably remove current_slr)
                    assert current_slr == sl.rects[-1]

                if different_widths_in_bin:
                    pass
                    #logger.warning( f"Different widths: {layer} {sl}")

    def check_shorts_induced_by_vias( self):

        for (via, (mv,mh)) in self.canvas.layer_stack:
            if via in self.store_scan_lines:
                for (twice_center, via_scan_line) in self.store_scan_lines[via].items():
                    assert mv is not None, "PLEASE IMPLEMENT ME !"
                    if twice_center not in self.store_scan_lines[mv]:
                        logger.warning( f"{twice_center} not in self.store_scan_lines[{mv}]. Skipping...")
                        continue
                    metal_scan_line_vertical = self.store_scan_lines[mv][twice_center]
                    for via_rect in via_scan_line.rects:
                        metal_rect_v = metal_scan_line_vertical.find_touching(via_rect)
                        twice_center_y = via_rect.rect[1] + via_rect.rect[3]
                        if mh is not None:
                            metal_scan_line_horizontal = self.store_scan_lines[mh][twice_center_y]
                            metal_rect_h = metal_scan_line_horizontal.find_touching(via_rect)
                            self.connectPair( via, metal_rect_v.root(), via_rect.root())
                            self.connectPair( via, via_rect.root(), metal_rect_h.root())
                        else:
                            self.connectPair( via, metal_rect_v.root(), via_rect.root())

    def check_shorts_induced_by_terminals( self):
        for instance, v in self.subinsts.items():
            for pin, slrs in v.pins.items():
                names = {x.root().netName for x in slrs}
                if len(names) > 1:
                    self.shorts.append( (names, f'THROUGH TERMINAL {instance}:{pin}', slrs) )

    def connectPair( self, layer, a, b):
        numshorts = len(self.shorts)
        if a.netName is None:
            a.netName = b.netName
            a.connect( b)
        elif b.netName is None or a.netName == b.netName:
            b.netName = a.netName
            a.connect( b)
        else:
            self.shorts.append( f'CONNECTPAIR {layer} {a} {b}' )
        if a.terminal is None and b.terminal is None:
            return numshorts == len(self.shorts)
        else:
            if a.terminal is not None:
                self.subinsts[a.terminal[0]].pins[a.terminal[1]].add( a)
            if b.terminal is not None:
                self.subinsts[b.terminal[0]].pins[b.terminal[1]].add( b)
            return False

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
        for layer, vv in self.store_scan_lines.items():
            for _, v in vv.items():
                for slr in v.rects:
                    root = slr.root()
                    terminals.append( {'layer': layer, 'netName': root.netName, 'rect': slr.rect, 'netType':slr.netType})
                    if slr.isPorted:
                        terminals[-1]['pin'] = root.netName
                    if slr.terminal is not None:
                        terminals[-1]['terminal'] = slr.terminal

        return terminals

    def remove_duplicates( self, silence_errors=False):

        self.build_scan_lines( self.build_centerline_tbl())

        self.check_shorts_induced_by_vias()
        self.check_shorts_induced_by_terminals()
        self.check_opens()

        # Trying fewer error messages
        if True:
            if self.shorts or self.opens or self.different_widths:
                if silence_errors:
                    logger.debug(f'Found errors: SHORT: {len(self.shorts)} OPEN: {len(self.opens)} DIFFERENT WIDTH: {len(self.different_widths)}')
                else:
                    logger.error(f'Found errors: SHORT: {len(self.shorts)} OPEN: {len(self.opens)} DIFFERENT WIDTH: {len(self.different_widths)}')
        else:
            for short in self.shorts:
                logger.warning("SHORT" + pprint.pformat(short))
            for opn in self.opens:
                logger.warning( "OPEN" + pprint.pformat(opn))
            for dif in self.different_widths:
                logger.warning( "DIFFERENT WIDTH" + pprint.pformat(dif))

        for subinst in self.subinsts:
            logger.debug("SUBINST" + pprint.pformat(subinst))

        return self.generate_rectangles()

