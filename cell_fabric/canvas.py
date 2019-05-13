import copy
import collections

from . import transformation
from . import generators
from . import remove_duplicates

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
        return remove_duplicates.remove_duplicates( self)
