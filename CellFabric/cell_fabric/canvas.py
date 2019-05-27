import copy
import collections

from . import transformation
from . import generators
from .remove_duplicates import RemoveDuplicates

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
 
    def transform_and_add( self, s):
        r = transformation.Rect( *s['rect'])
        s['rect'] = self.trStack[-1].hitRect(r).canonical().toList()
        self.terminals.append( s)

    def addWire( self, wire, netName, pinName, c, bIdx, eIdx, *, bS=None, eS=None):
        self.transform_and_add( wire.segment( netName, pinName, c, bIdx, eIdx, bS=bS, eS=eS))
       
    def addRegion( self, region, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1):
        self.transform_and_add( region.segment( netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1))

    def addVia( self, via, netName, pinName, cx, cy):
        self.transform_and_add( via.segment( netName, pinName, cx, cy))

    def addWireAndViaSet( self, netName, wire, via, c, listOfIndices, *, bIdx=None, eIdx=None):
        """March through listOfIdx, compute physical coords (including via extensions), keep bounding box, draw wire."""
        self.addWireAndMultiViaSet( netName, wire, c, [ (via, listOfIndices)], bIdx=bIdx, eIdx=eIdx)

    def addWireAndMultiViaSet( self, netName, wire, c, listOfPairs, *, bIdx=None, eIdx=None):
        """March through listOfPairs (via, idx), compute physical coords (including via extensions), keep bounding box, draw wire."""

        tuples = [(via.v_clg if wire.direction == 'h' else via.h_clg).value(idx, check=False)[0] for (via,listOfIndices) in listOfPairs for idx in listOfIndices]

#
# Find min and max indices (using physical coordinate as key)
#
        mnP = min(tuples)
        mxP = max(tuples)

# should be the real enclosure but this finds the next grid point
        enclosure = 1
        (mn, _) = wire.spg.inverseBounds( mnP-enclosure)
        (_, mx) = wire.spg.inverseBounds( mxP+enclosure)

        for (via,listOfIndices) in listOfPairs:
            for q in listOfIndices:
                if wire.direction == 'v':
                    self.addVia( via, netName, None, c, q)
                else:
                    self.addVia( via, netName, None, q, c)

        self.addWire( wire, netName, None, c, mn, mx)

    def asciiStickDiagram( self, v1, m2, v2, m3, matrix, *, xpitch=4, ypitch=2):
        # clean up text input
        a = matrix.split( '\n')[1:-1]

        ncols = max([ len(row) for row in a])
        assert (ncols-1) % xpitch == 0
        nrows = len(a)
        assert (nrows-1) % ypitch == 0

        paddedA = []
        for row in a:
            paddedA.append( row + ' '*(ncols-len(row)))
        assert max([ len(row) for row in paddedA]) == ncols

        for x in range(ncols):
            for y in range(nrows):
                if x % xpitch != 0 and y % ypitch != 0:
                    assert paddedA[y][x] == ' '

        # find all metal2
        for y in reversed(range( (nrows-1) // ypitch + 1)):
            row = paddedA[nrows-1-y*ypitch] + ' '
            started = False
            nm = None
            via1s = []
            via2s = []

            for (x,c) in enumerate( row):
                if c == ' ':
                    if started:
                        # close off wire
                        assert nm is not None
                        self.addWireAndMultiViaSet( nm, m2, y, [ (v1, via1s), (v2, via2s)]) 
                        started = False
                        nm = None
                        via1s = []
                        via2s = []
                elif c in ['+','*']:
                    assert x % xpitch == 0
                    via1s.append( x//xpitch)
                    started = True
                elif c in ['/','*']:
                    assert x % xpitch == 0
                    via2s.append( x//xpitch)
                    started = True
                elif c in ['=']:
                    assert started
                elif c in ['|']:
                    pass
                else:
                    if started:
                        if nm is None:
                            nm = c
                        else:
                            nm = nm + c

        # find all metal3
        for x in range( (ncols-1) // xpitch + 1):
            col = ''.join([ paddedA[nrows-1-y][x*xpitch] for y in range(nrows)]) + ' '
            started = False
            nm = None
            via2s = []

            for (y,c) in enumerate( col):
                if c == ' ':
                    if started:
                        # close off wire
                        assert nm is not None
                        self.addWireAndMultiViaSet( nm, m3, x, [ (v2, via2s)]) 
                        started = False
                        nm = None
                        via1s = []
                        via2s = []
                elif c in ['/','*']:
                    assert y % ypitch == 0
                    via2s.append( y//ypitch)
                    started = True
                elif c in ['|']:
                    assert started
                elif c in ['=','+']:
                    pass
                else: # bottom up traversal so construct the name in reverse
                    if started:
                        if nm is None:
                            nm = c
                        else:
                            nm = c + nm

    def __init__( self):
        self.terminals = []
        self.generators = collections.OrderedDict()
        self.trStack = [transformation.Transformation()]

    def pushTr( self, tr):
        self.trStack.append( self.trStack[-1].postMult( tr))

    def hitTopTr( self, tr):
        self.trStack[-1] = self.trStack[-1].postMult( tr)

    def popTr( self):
        self.trStack.pop()
        assert self.trStack != []

    def removeDuplicates( self):
        self.rd = RemoveDuplicates( self)
        return self.rd.remove_duplicates()
