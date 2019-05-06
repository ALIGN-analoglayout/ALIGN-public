"""
Nine Track fabric with shared power rails
"""

import json
import transformation

class StopPointGrid:
    def __init__( self, nm, layer, direction, *, width, pitch, offset=0):
        self.nm = nm
        self.layer = layer
        self.direction = direction
        assert direction in ['v','h']
        self.width = width
        self.pitch = pitch
        self.offset = offset
        assert pitch > width > 0

        self.grid = []
        self.legalStopVector = []
        self.legalStopIndices = set()

    def addGridPoint( self, value, isLegal):
        self.grid.append( value)
        self.legalStopVector.append( isLegal)
        if isLegal:
            self.legalStopIndices.add( len(self.grid)-1)

    @property
    def n( self):
        return len(self.grid)-1

    def value( self, idx):
        whole = idx // self.n
        fract = idx % self.n
        while fract < 0:
            whole -= 1
            fract += self.n
        assert fract in self.legalStopIndices
        return whole * self.grid[-1] + self.grid[fract]

    def segment( self, netName, center, bIdx, eIdx):
        c = center*self.pitch + self.offset
        c0 = c - self.width//2
        c1 = c + self.width//2
        if self.direction == 'h':
            rect = [ self.value(bIdx), c0, self.value(eIdx), c1]
        else:
            rect = [ c0, self.value(bIdx), c1, self.value(eIdx)]
        return { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

class Canvas:

    def computeBbox( self):
        self.bbox = transformation.Rect(None,None,None,None)
        for term in self.terminals:
            r = transformation.Rect( *term['rect'])
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

    def __init__( self):
        self.terminals = []

        self.finsPerUnitCell = 12
        # Must be a multiple of 2
        assert self.finsPerUnitCell % 2 == 0
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0

        self.m2PerUnitCell = 9

        m2Pitch  = 720 

        unitCellHeight = self.m2PerUnitCell*m2Pitch

        pcPitch  = 720
        m1Pitch  = 720 
#        m3Pitch  = 720 

        plPitch  = m1Pitch
        plOffset = plPitch//2
        dcPitch  = 2*m1Pitch

        pcWidth = 200
        m1Width = 400
        m2Width = 400
#        m3Width = 400
        dcWidth = 200
        plWidth = 200

        ndWidth = 120
        ndPitch = 360

        stoppoint = plOffset-plWidth//2
        self.nd = StopPointGrid( 'nd', 'ndiff', 'h', width=ndWidth, pitch=ndPitch)
        self.nd.addGridPoint( 0,                 True)
        self.nd.addGridPoint( dcPitch,           True)

        stoppoint = plOffset-plWidth//2
        self.pc = StopPointGrid( 'pc', 'polycon', 'h', width=pcWidth, pitch=pcPitch, offset=pcPitch//2)
        self.pc.addGridPoint( 0,                 False)
        self.pc.addGridPoint( stoppoint,         True)
        self.pc.addGridPoint( dcPitch//2,        False)
        self.pc.addGridPoint( dcPitch-stoppoint, True)
        self.pc.addGridPoint( dcPitch,           False)

        stoppoint = unitCellHeight//2-m2Pitch-m2Pitch//2
        self.m1 = StopPointGrid( 'm1', 'metal1', 'v', width=m1Width, pitch=m1Pitch)
        self.m1.addGridPoint( 0,                                False)
        self.m1.addGridPoint( stoppoint,                        True)
        self.m1.addGridPoint( stoppoint+m2Pitch,                True)
        self.m1.addGridPoint( unitCellHeight//2,                False)
        self.m1.addGridPoint( unitCellHeight-stoppoint-m2Pitch, True)
        self.m1.addGridPoint( unitCellHeight-stoppoint,         True)
        self.m1.addGridPoint( unitCellHeight,                   False)

        stoppoint = m1Pitch//2
        self.m2 = StopPointGrid( 'm2', 'metal2', 'h', width=m2Width, pitch=m2Pitch, offset=m2Pitch//2)
        self.m2.addGridPoint( 0,                 False)
        self.m2.addGridPoint( stoppoint,         True)
        self.m2.addGridPoint( m1Pitch,           False)

        stoppoint = m2Pitch//2
        self.pl = StopPointGrid( 'pl', 'poly', 'v', width=plWidth, pitch=plPitch, offset=plOffset)
        self.pl.addGridPoint( 0,                           False)
        self.pl.addGridPoint( stoppoint-plWidth//2,        True)
        self.pl.addGridPoint( unitCellHeight//2-stoppoint, True)
        self.pl.addGridPoint( unitCellHeight//2,           False)
        self.pl.addGridPoint( unitCellHeight//2+stoppoint, True)
        self.pl.addGridPoint( unitCellHeight-stoppoint+plWidth//2,    True)
        self.pl.addGridPoint( unitCellHeight,              False)

        stoppoint = m1Pitch//2
        self.dc = StopPointGrid( 'dc', 'diffcon', 'v', width=dcWidth, pitch=dcPitch)
        self.dc.addGridPoint( 0,                           False)
        self.dc.addGridPoint( stoppoint,                   True)
        self.dc.addGridPoint( unitCellHeight//2-stoppoint, True)
        self.dc.addGridPoint( unitCellHeight//2,           False)
        self.dc.addGridPoint( unitCellHeight//2+stoppoint, True)
        self.dc.addGridPoint( unitCellHeight-stoppoint,    True)
        self.dc.addGridPoint( unitCellHeight,              False)

    def addSegment( self, grid, netName, c, bIdx, eIdx):
        def f( idx):
            if isinstance(idx) is tuple:
                return idx[1] + grid.n*idx[0]
            else:
                return idx
        segment = grid.segment( netName, c, f(bIdx), f(eIdx))
        self.terminals.append( segment)
        return segment
        
    def pcSegment( self, netName, x0, x1, y): return self.addSegment( self.pc, netName, y, x0, x1)
    def m1Segment( self, netName, x, y0, y1): return self.addSegment( self.m1, netName, x, y0, y1)
    def m2Segment( self, netName, x0, x1, y): return self.addSegment( self.m2, netName, y, x0, x1)
    def plSegment( self, netName, x, y0, y1): return self.addSegment( self.pl, netName, x, y0, y1)
    def dcSegment( self, netName, x, y0, y1): return self.addSegment( self.dc, netName, x, y0, y1)
    def ndSegment( self, netName, x0, x1, y): return self.addSegment( self.nd, netName, y, x0, x1)

    def nunit( self, x, y):
        for o in range(self.finsPerUnitCell//2):
            self.ndSegment( '_', 1*(x+0), 1*(x+1), 2*self.m2PerUnitCell*y+(2+o))
            self.ndSegment( '_', 1*(x+0), 1*(x+1), 2*self.m2PerUnitCell*y-(2+o))

        (ds0,ds1) = ('s', 'd') if x % 2 == 0 else ('d','s')

        assert self.dc.n == 6
        assert self.pl.n == 6
        assert self.pc.n == 4
        assert self.m1.n == 6

        self.dcSegment( ds0, 1*(x+0), (y,-2), (y,-1))
        self.dcSegment( ds0, 1*(x+0), (y, 1), (y, 2))
        self.plSegment( 'g', 2*x+0,   (y,-2), (y,-1))
        self.plSegment( 'g', 2*x+0,   (y, 1), (y, 2))
        self.plSegment( 'g', 2*x+1,   (y,-2), (y,-1))
        self.plSegment( 'g', 2*x+1,   (y, 1), (y, 2))
        self.dcSegment( ds1, 1*(x+1), (y,-2), (y,-1))
        self.dcSegment( ds1, 1*(x+1), (y, 1), (y, 2))

        self.pcSegment( 'g', (x, 1), ((x+1),-1), self.m2PerUnitCell*y-1)
        self.pcSegment( 'g', (x, 1), ((x+1),-1), self.m2PerUnitCell*y+0)

        self.m1Segment( ds0, 2*(x+0)+0, (y,-1), (y, 1))
        self.m1Segment( 'g', 2*(x+0)+1, (y,-2), (y, 2))
        self.m1Segment( ds1, 2*(x+1)+0, (y,-1), (y, 1))

        assert self.m2PerUnitCell % 2 == 1

        h = self.m2PerUnitCell//2
        for o in range(-h-1,h+1):
            self.m2Segment( '_', 4*x-1, 4*(x+1)+1, self.m2PerUnitCell*y+o)


import argparse

def test_nunit():
    c = Canvas()

    for (x,y) in ( (x,y) for x in range(12) for y in range(1)):
        c.nunit( x, y)

    c.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : c.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : c.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')




if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Build test device and cap fabrics")
    parser.add_argument( "-n", "--block_name", type=str, required=True)
    args = parser.parse_args()

    if args.block_name == "nunit":
        test_nunit()
    else:
        assert False
