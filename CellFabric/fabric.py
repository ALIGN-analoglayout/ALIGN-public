
import json

def write_global_routing_json( fp, terminals):


    data = { 'bbox' : [0,0,10000,10000], 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : terminals}
    fp.write( json.dumps( data, indent=2) + '\n')

class UnitCell():

    def __init__( self):
        self.terminals = []

        self.m0Pitch    = 360
        self.m1Pitch    = 720 
        self.polyPitch  = 720
        self.diffconPitch  = 720

        self.m1Width = 400
        self.m0Width = 200
        self.diffconWidth = 200
        self.polyWidth = 200

        stoppoint = (self.diffconWidth//2 + self.polyOffset-self.polyWidth//2)//2
        self.m0Grid = [ 0, stoppoint, self.polyOffset, self.diffconPitch-stoppoint, self.diffconPitch]
        self.m0GridStops = [False,True,False,True,False]
        self.m0GridStopIndices = set([1,3])

        stoppoint = (self.m0Width//2 + self.m0Pitch-self.m0Width//2)//2
        self.m1Grid = [ 0, stoppoint, 2*self.m0Pitch, 4*self.m0Pitch-stoppoint, 4*self.m0Pitch]
        self.m1GridStops = [False,True,False,True,False]
        self.m1GridStopIndices = set([1,3])

        self.polyGrid = [ 0, stoppoint, 2*self.m0Pitch, 4*self.m0Pitch-stoppoint, 4*self.m0Pitch]
        self.polyGridStops = [False,True,False,True,False]
        self.polyGridStopIndices = set([1,3])

        self.diffconGrid = [ 0, stoppoint, 2*self.m0Pitch, 4*self.m0Pitch-stoppoint, 4*self.m0Pitch]
        self.diffconGridStops = [False,True,False,True,False]
        self.diffconGridStopIndices = set([1,3])
        

    @property
    def polyOffset( self):
        return self.polyPitch // 2

    def m0x( self, x):
        xWhole = x // (len(self.m0Grid)-1)
        xFract = x % (len(self.m0Grid)-1)
        while xFract < 0:
            xWhole -= 1
            xFract += len(self.m0Grid)-1
        assert xFract in self.m0GridStopIndices
        return xWhole * self.m0Grid[-1] + self.m0Grid[xFract]

    def m1y( self, y):
        yWhole = y // (len(self.m1Grid)-1)
        yFract = y % (len(self.m1Grid)-1)
        while yFract < 0:
            yWhole -= 1
            yFract += len(self.m1Grid)-1
        assert yFract in self.m1GridStopIndices
        return yWhole * self.m1Grid[-1] + self.m1Grid[yFract]

    def polyy( self, y):
        yWhole = y // (len(self.polyGrid)-1)
        yFract = y % (len(self.polyGrid)-1)
        while yFract < 0:
            yWhole -= 1
            yFract += len(self.polyGrid)-1
        assert yFract in self.polyGridStopIndices
        return yWhole * self.polyGrid[-1] + self.polyGrid[yFract]

    def diffcony( self, y):
        yWhole = y // (len(self.diffconGrid)-1)
        yFract = y % (len(self.diffconGrid)-1)
        while yFract < 0:
            yWhole -= 1
            yFract += len(self.diffconGrid)-1
        assert yFract in self.diffconGridStopIndices
        return yWhole * self.diffconGrid[-1] + self.diffconGrid[yFract]

    def m0Segment( self, netName, x0, x1, y):
        yc = y*self.m0Pitch
        y0 = yc - self.m0Width//2
        y1 = yc + self.m0Width//2
        rect = [ self.m0x(x0), y0, self.m0x(x1), y1]
        segment = { 'netName' : netName, 'layer' : 'metal0', 'rect' : rect}
        self.terminals.append( segment)
        return segment

    def m1Segment( self, netName, x, y0, y1):
        xc = x*self.m1Pitch
        x0 = xc - self.m1Width//2
        x1 = xc + self.m1Width//2
        rect = [x0, self.m1y(y0), x1, self.m1y(y1)]
        segment = { 'netName' : netName, 'layer' : 'metal1', 'rect' : rect}
        self.terminals.append( segment)
        return segment

    def polySegment( self, netName, x, y0, y1):
        xc = x*self.polyPitch + self.polyOffset
        x0 = xc - self.polyWidth//2
        x1 = xc + self.polyWidth//2
        rect = [x0, self.polyy(y0), x1, self.polyy(y1)]
        segment = { 'netName' : netName, 'layer' : 'poly', 'rect' : rect}
        self.terminals.append( segment)
        return segment

    def diffconSegment( self, netName, x, y0, y1):
        xc = x*self.diffconPitch
        x0 = xc - self.diffconWidth//2
        x1 = xc + self.diffconWidth//2
        rect = [x0, self.diffcony(y0), x1, self.diffcony(y1)]
        segment = { 'netName' : netName, 'layer' : 'diffcon', 'rect' : rect}
        self.terminals.append( segment)
        return segment

    def unit( self, x, y):
        uc.diffconSegment( 's',   2*x+0, 4*y+1, 4*y+3)
        uc.polySegment(    'g',   2*x+0, 4*y+1, 4*y+3)
        uc.polySegment(    'g',   2*x+1, 4*y+1, 4*y+3)
        uc.diffconSegment( 'd',   2*x+2, 4*y+1, 4*y+3)

        uc.m0Segment( 's', 8*x-3, 8*x+3,  4*y+1)
        uc.m0Segment( 's', 8*x-3, 8*x+3,  4*y+3)
        uc.m0Segment( 'g', 8*x+1, 8*x+7,  4*y+2)
        uc.m0Segment( 'd', 8*x+5, 8*x+11, 4*y+1)
        uc.m0Segment( 'd', 8*x+5, 8*x+11, 4*y+3)

        uc.m0Segment( 'gnd', 8*x-1, 8*x+9, 4*y+0)
        uc.m0Segment( 'gnd', 8*x-1, 8*x+9, 4*y+4)

        uc.m1Segment( 's', 2*x+0, 4*y+1, 4*y+3)
        uc.m1Segment( 'g', 2*x+1, 4*y+1, 4*y+3)
        uc.m1Segment( 'd', 2*x+2, 4*y+1, 4*y+3)

if __name__ == "__main__":
    uc = UnitCell()

    for (x,y) in ( (x,y) for x in range(16) for y in range(16)):
        uc.unit( x, y)

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        write_global_routing_json( fp, uc.terminals)
