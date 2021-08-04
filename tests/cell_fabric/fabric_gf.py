
import json

from align.cell_fabric import Grid, SingleGrid, EnclosureGrid
from align.cell_fabric import UncoloredCenterLineGrid
from align.cell_fabric import Canvas, Wire

class CanvasNMOS(Canvas):

    def __init__( self):
        super().__init__()

        self.finsPerUnitCell = 12
        # Must be a multiple of 2
        assert self.finsPerUnitCell % 2 == 0
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0

        self.m2PerUnitCell = self.finsPerUnitCell//2 + 3

        m2Pitch  = 720 

        unitCellHeight = self.m2PerUnitCell*m2Pitch

        pcPitch  = unitCellHeight//2
        m1Pitch  = 720 
        m3Pitch  = 720 

        plPitch  = m1Pitch
        plOffset = plPitch//2
        dcPitch  = 2*m1Pitch

        pcWidth = 200
        m1Width = 400
        m2Width = 400
        m3Width = 400
        dcWidth = 200
        plWidth = 200

        ndWidth = 120
        ndPitch = 360

        self.nd = self.addGen( Wire( 'nd', 'ndiff', 'h',
                                     clg=UncoloredCenterLineGrid( pitch=ndPitch, width=ndWidth, repeat=2*self.m2PerUnitCell),
                                     spg=SingleGrid( pitch=dcPitch)))

        self.pc = self.addGen( Wire( 'pc', 'polycon', 'h',
                                     clg=UncoloredCenterLineGrid( width=pcWidth, pitch=pcPitch),
                                     spg=EnclosureGrid( pitch=dcPitch, stoppoint=plOffset-plWidth//2)))

        self.m1 = self.addGen( Wire( 'm1', 'M1', 'v',
                                     clg=UncoloredCenterLineGrid( width=m1Width, pitch=m1Pitch, repeat=2),
                                     spg=EnclosureGrid( pitch=unitCellHeight, stoppoint=unitCellHeight//2-m2Pitch)))

        self.m3 = self.addGen( Wire( 'm3', 'M3', 'v',
                                     clg=UncoloredCenterLineGrid( width=m3Width, pitch=m3Pitch, repeat=2),
                                     spg=EnclosureGrid( pitch=unitCellHeight, stoppoint=unitCellHeight//2-m2Pitch)))

        self.m2 = self.addGen( Wire( 'm2', 'M2', 'h',
                                     clg=UncoloredCenterLineGrid( width=m2Width, pitch=m2Pitch, repeat=self.m2PerUnitCell),
                                     spg=EnclosureGrid( pitch=2*m1Pitch, stoppoint=m1Pitch//2)))


        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( width=plWidth, pitch=plPitch, offset=plOffset, repeat=2),
                                     spg=EnclosureGrid(  pitch=unitCellHeight, stoppoint=m1Pitch//2)))


        self.dc = self.addGen( Wire( 'dc', 'diffcon', 'v',
                                     clg=UncoloredCenterLineGrid( width=dcWidth, pitch=dcPitch),
                                     spg=Grid()))
        stoppoint=m1Pitch//2
        self.dc.spg.addGridLine( 0,                           False)
        self.dc.spg.addGridLine( stoppoint,                   True)
        self.dc.spg.addGridLine( unitCellHeight//2-stoppoint, True)
        self.dc.spg.addGridLine( unitCellHeight//2,           False)
        self.dc.spg.addGridLine( unitCellHeight//2+stoppoint, True)
        self.dc.spg.addGridLine( unitCellHeight-stoppoint,    True)
        self.dc.spg.addGridLine( unitCellHeight,              False)

    def nunit( self, x, y):
        for o in range(self.finsPerUnitCell//2):
            self.addWire( self.nd, '_', (y,  (2+o)), (x, 0), (x, 1))
            self.addWire( self.nd, '_', (y, -(2+o)), (x, 0), (x, 1))

        (ds0,ds1) = ('s', 'd') if x % 2 == 0 else ('d','s')

        self.addWire( self.dc, ds0, x+0, (y,-2), (y,-1))
        self.addWire( self.dc, ds0, x+0, (y, 1), (y, 2))

        self.addWire( self.pl, 'g', (x, 0), (y,-1), (y, 1))
        self.addWire( self.pl, 'g', (x, 1), (y,-1), (y, 1))

        self.addWire( self.dc, ds1, x+1, (y,-2), (y,-1))
        self.addWire( self.dc, ds1, x+1, (y, 1), (y, 2))

        self.addWire( self.pc, 'g', (y, 0), (x, 1), ((x+1),-1))

        self.addWire( self.m1, ds0, (x+0, 0), (y,-1), (y, 1))
        self.addWire( self.m1, 'g', (x+0, 1), (y,-1), (y, 1))
        self.addWire( self.m1, ds1, (x+1, 0), (y,-1), (y, 1))

        assert self.m2PerUnitCell % 2 == 1

        h = self.m2PerUnitCell//2
        for o in range(-h,h+1):
            self.addWire( self.m2, '_', (y, o), (x, -1), (x+1, 1))

    def cunit( self, x, y):

        for o in range(self.finsPerUnitCell//2):
            self.addWire( self.nd, '_', (y,  (2+o)), (x, 0), (x, 1))
            self.addWire( self.nd, '_', (y, -(2+o)), (x, 0), (x, 1))

        self.addWire( self.dc, 't0', x+0, (y,-2), (y,-1))
        self.addWire( self.dc, 't0', x+0, (y, 1), (y, 2))

        self.addWire( self.pl, 't1', (x, 0), (y,-1), (y, 1))
        self.addWire( self.pl, 't1', (x, 1), (y,-1), (y, 1))

        self.addWire( self.dc, 't0', x+1, (y,-2), (y,-1))
        self.addWire( self.dc, 't0', x+1, (y, 1), (y, 2))

        self.addWire( self.pc, 't1', (y, 0), (x, 1), ((x+1),-1))

        self.addWire( self.m1, 't0', (x+0, 0), (y,-1), (y, 1))
        self.addWire( self.m1, 't1', (x+0, 1), (y,-1), (y, 1))
        self.addWire( self.m1, 't0', (x+1, 0), (y,-1), (y, 1))

        self.addWire( self.m3, 't0', (x+0, 0), (y,-1), (y, 1))
        self.addWire( self.m3, 't1', (x+0, 1), (y,-1), (y, 1))
        self.addWire( self.m3, 't0', (x+1, 0), (y,-1), (y, 1))

        assert self.m2PerUnitCell % 2 == 1

        h = self.m2PerUnitCell//2
        for o in range(-h,h+1):
            net = 't1' if o % 2 == 0 else 't0'
            self.addWire( self.m2, net, (y, o), (x, -1), (x+1, 1))


import argparse

def test_nunit():
    c = Canvas()

    for (x,y) in ( (x,y) for x in range(2) for y in range(1)):
        c.nunit( x, y)

    c.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : c.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : c.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

def test_cunit():
    c = Canvas()

    for (x,y) in ( (x,y) for x in range(16) for y in range(4)):
        c.cunit( x, y)

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
    elif args.block_name == "cunit":
        test_cunit()
