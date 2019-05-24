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
        """March through listOfIdx, compute physical coords (including via extensions), keep bounding box."""

        def bounds( v, bound):
            (q,(lt,ge)) = wire.spg.inverseValue( v)
            assert ge is not None
            geValue = wire.spg.value( (q,ge), check=False)[0]

            assert bound in ['u','l']
            result = (q,ge)
            if bound == 'l' and v < geValue:
                assert lt is not None
                result = (q,lt)

            return result

        via_clg = via.v_clg if wire.direction == 'h' else via.h_clg

#
# Find min and max indices (using physical coordinate as key)
#
        tuples = [ (via_clg.value( idx, check=False), idx) for idx in listOfIndices]
        mnP = via_clg.value( min(tuples)[1], check=False)[0]
        mxP = via_clg.value( max(tuples)[1], check=False)[0]

# should be the real enclosure but this finds the next grid point
        enclosure = 1
        mn = bounds( mnP-enclosure, 'l')
        mx = bounds( mxP+enclosure, 'u')

        for q in listOfIndices:
            if wire.direction == 'v':
                self.addVia( via, netName, None, c, q)
            else:
                self.addVia( via, netName, None, q, c)

        self.addWire( wire, netName, None, c, mn, mx)

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
        rd = RemoveDuplicates( self)
        return rd.remove_duplicates()
