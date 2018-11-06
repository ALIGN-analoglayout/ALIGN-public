
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

class UnitCell:

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

        m0Pitch  = 360
        m1Pitch  = 720 
        plPitch  = 720
        plOffset = plPitch//2
        dcPitch  = 720

        assert dcPitch == plPitch

        m1Width = 400
        m0Width = 200
        dcWidth = 200
        plWidth = 200

        stoppoint = (dcWidth//2 + plOffset-plWidth//2)//2
        self.m0 = StopPointGrid( 'm0', 'metal0', 'h', width=m0Width, pitch=m0Pitch)
        self.m0.addGridPoint( 0,                 False)
        self.m0.addGridPoint( stoppoint,         True)
        self.m0.addGridPoint( plOffset,          False)
        self.m0.addGridPoint( dcPitch-stoppoint, True)
        self.m0.addGridPoint( dcPitch,           False)

        stoppoint = (m0Width//2 + m0Pitch-m0Width//2)//2
        self.m1 = StopPointGrid( 'm1', 'metal1', 'v', width=m1Width, pitch=m1Pitch)
        self.m1.addGridPoint( 0,                   False)
        self.m1.addGridPoint( stoppoint,           True)
        self.m1.addGridPoint( 2*m0Pitch,           False)
        self.m1.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.m1.addGridPoint( 4*m0Pitch,           False)

        self.pl = StopPointGrid( 'pl', 'poly', 'v', width=plWidth, pitch=plPitch, offset=plOffset)
        self.pl.addGridPoint( 0,                   False)
        self.pl.addGridPoint( stoppoint,           True)
        self.pl.addGridPoint( 2*m0Pitch,           False)
        self.pl.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.pl.addGridPoint( 4*m0Pitch,           False)

        self.dc = StopPointGrid( 'dc', 'diffcon', 'v', width=dcWidth, pitch=dcPitch)
        self.dc.addGridPoint( 0,                   False)
        self.dc.addGridPoint( stoppoint,           True)
        self.dc.addGridPoint( 2*m0Pitch,           False)
        self.dc.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.dc.addGridPoint( 4*m0Pitch,           False)

    def addSegment( self, grid, netName, c, bIdx, eIdx):
        segment = grid.segment( netName, c, bIdx, eIdx)
        self.terminals.append( segment)
        return segment
        
    def m0Segment( self, netName, x0, x1, y): return self.addSegment( self.m0, netName, y, x0, x1)
    def m1Segment( self, netName, x, y0, y1): return self.addSegment( self.m1, netName, x, y0, y1)
    def plSegment( self, netName, x, y0, y1): return self.addSegment( self.pl, netName, x, y0, y1)
    def dcSegment( self, netName, x, y0, y1): return self.addSegment( self.dc, netName, x, y0, y1)

    def unit( self, x, y):
        ny = 4
        nx = 8
        ncx = 2
        ncy = 4
        uc.dcSegment( 's', ncx*(x+0)+0, ny*(y+0)+1, ny*(y+1)-1)
        uc.plSegment( 'g', ncx*(x+0)+0, ny*(y+0)+1, ny*(y+1)-1)
        uc.plSegment( 'g', ncx*(x+0)+1, ny*(y+0)+1, ny*(y+1)-1)
        uc.dcSegment( 'd', ncx*(x+1)+0, ny*(y+0)+1, ny*(y+1)-1)

        uc.m0Segment( 's', nx*(x+0)-3, nx*(x+0)+3, ncy*(y+0)+1)
        uc.m0Segment( 's', nx*(x+0)-3, nx*(x+0)+3, ncy*(y+1)-1)
        uc.m0Segment( 'g', nx*(x+0)+1, nx*(x+1)-1, ncy*(y+0)+2)
        uc.m0Segment( 'd', nx*(x+1)-3, nx*(x+1)+3, ncy*(y+0)+1)
        uc.m0Segment( 'd', nx*(x+1)-3, nx*(x+1)+3, ncy*(y+1)-1)

        uc.m0Segment( 'gnd', nx*x-1, nx*x+9, ncy*(y+0)+0)
        uc.m0Segment( 'gnd', nx*x-1, nx*x+9, ncy*(y+1)+0)

        uc.m1Segment( 's', ncx*(x+0)+0, ny*(y+0)+1, ny*(y+1)-1)
        uc.m1Segment( 'g', ncx*(x+0)+1, ny*(y+0)+1, ny*(y+1)-1)
        uc.m1Segment( 'd', ncx*(x+1)+0, ny*(y+0)+1, ny*(y+1)-1)

if __name__ == "__main__":
    uc = UnitCell()

    for (x,y) in ( (x,y) for x in range(16) for y in range(16)):
        uc.unit( x, y)

    uc.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
