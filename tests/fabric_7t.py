
import json

from cell_fabric import Grid, SingleGrid, EnclosureGrid, CenteredGrid
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import Canvas as AbstractCanvas
from cell_fabric import Wire, Via, Region

class Canvas(AbstractCanvas):

    def __init__( self):
        super().__init__()

        self.finsPerUnitCell = 14
        self.m2PerUnitCell = 7

        ndPitch = 360
        pdPitch = 360

        m2Pitch = 720 

        unitCellHeight = self.m2PerUnitCell*m2Pitch

        pcPitch  = unitCellHeight//2
        m1Pitch  = 864
        m1hPitch  = m2Pitch
        m3Pitch  = 720 

        plPitch  = m1Pitch
        plOffset = plPitch//2
        dcPitch  = m1Pitch

        pcWidth = 200
        m1Width = 400
        m2Width = 400
        m3Width = 400
        dcWidth = 200
        plWidth = 200

        ndWidth = 120
        ndPitch = 360

        self.nd = self.addGen( Region( 'nd', 'ndiff',
                                       h_grid=SingleGrid( pitch=ndPitch),
                                       v_grid=SingleGrid( pitch=dcPitch, offset=dcPitch//2)))

        self.pd = self.addGen( Region( 'pd', 'pdiff',
                                       h_grid=SingleGrid( pitch=pdPitch),
                                       v_grid=SingleGrid( pitch=dcPitch, offset=dcPitch//2)))

        self.pc = self.addGen( Wire( 'pc', 'polycon', 'h',
                                     clg=UncoloredCenterLineGrid( width=pcWidth, pitch=pcPitch),
                                     spg=EnclosureGrid( pitch=dcPitch, stoppoint=plOffset-plWidth//2)))

        self.m1 = self.addGen( Wire( 'm1', 'M1', 'v',
                                     clg=UncoloredCenterLineGrid( width=m1Width, pitch=m1Pitch, repeat=2),
                                     spg=EnclosureGrid( pitch=m2Pitch, stoppoint=m2Width//2)))

        self.m2 = self.addGen( Wire( 'm2', 'M2', 'h',
                                     clg=UncoloredCenterLineGrid( width=m2Width, pitch=m2Pitch, repeat=self.m2PerUnitCell),
                                     spg=EnclosureGrid( pitch=2*m1Pitch, stoppoint=m1Pitch//2)))

        self.m3 = self.addGen( Wire( 'm3', 'M3', 'v',
                                     clg=UncoloredCenterLineGrid( width=m3Width, pitch=m3Pitch),
                                     spg=EnclosureGrid( pitch=unitCellHeight, stoppoint=unitCellHeight//2-m2Pitch)))


        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( width=plWidth, pitch=plPitch, offset=plOffset, repeat=2),
                                     spg=EnclosureGrid( pitch=m2Pitch//2, stoppoint=m2Width//2+16)))


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
        self.addRegion( self.nd, None, None, 2*x-1, ((y+0)*2*self.m2PerUnitCell,  2), 2*(x+1), ((y+0)*2*self.m2PerUnitCell,  6))
        self.addRegion( self.pd, None, None, 2*x-1, ((y+1)*2*self.m2PerUnitCell, -6), 2*(x+1), ((y+1)*2*self.m2PerUnitCell, -2))

        (ds0,ds1) = ('s', 'd') if x % 2 == 0 else ('d','s')

#        self.addWire( self.dc, ds0, None, x+0, (y,-2), (y,-1))
#        self.addWire( self.dc, ds0, None, x+0, (y, 1), (y, 2))

        self.addWire( self.pl, None, None, (x, -1), (y*2*self.m2PerUnitCell + 2,-1), (y*2*self.m2PerUnitCell + 6, 1))
        self.addWire( self.pl, 'g', None, (x, 0), (y*2*self.m2PerUnitCell + 2,-1), (y*2*self.m2PerUnitCell + 6, 1))
        self.addWire( self.pl, 'g', None, (x, 1), (y*2*self.m2PerUnitCell + 2,-1), (y*2*self.m2PerUnitCell + 6, 1))
        self.addWire( self.pl, None, None, (x, 2), (y*2*self.m2PerUnitCell + 2,-1), (y*2*self.m2PerUnitCell + 6, 1))

        self.addWire( self.pl, None, None, (x, -1), (y*2*self.m2PerUnitCell + 8, -1), (y*2*self.m2PerUnitCell + 12, 1))
        self.addWire( self.pl, 'g', None, (x, 0), (y*2*self.m2PerUnitCell + 8, -1), (y*2*self.m2PerUnitCell + 12, 1))
        self.addWire( self.pl, 'g', None, (x, 1), (y*2*self.m2PerUnitCell + 8, -1), (y*2*self.m2PerUnitCell + 12, 1))
        self.addWire( self.pl, None, None, (x, 2), (y*2*self.m2PerUnitCell + 8, -1), (y*2*self.m2PerUnitCell + 12, 1))

#        self.addWire( self.dc, ds1, None, x+1, (y,-2), (y,-1))
#        self.addWire( self.dc, ds1, None, x+1, (y, 1), (y, 2))

#        self.addWire( self.pc, 'g', None, (y, 0), (x, 1), ((x+1),-1))

        self.addWire( self.m1, ds0, None, (x+0, 0), (y*self.m2PerUnitCell + 1,-1), ((y+1)*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, 'g', None, (x+0, 1), (y*self.m2PerUnitCell + 1,-1), ((y+1)*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, ds1, None, (x+1, 0), (y*self.m2PerUnitCell + 1,-1), ((y+1)*self.m2PerUnitCell - 1, 1))

        assert self.m2PerUnitCell % 2 == 1

        for o in range(0,self.m2PerUnitCell+1):
            self.addWire( self.m2, '_', None, (y, o), (x, -1), (x+1, 1))
