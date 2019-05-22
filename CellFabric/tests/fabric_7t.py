
import json

from cell_fabric.transformation import Transformation
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

        self.unitCellHeight = self.m2PerUnitCell*m2Pitch


        pcPitch  = self.unitCellHeight//2
        m1Pitch  = 864
        m1hPitch  = m2Pitch
        m3Pitch  = 720 
        self.unitCellWidth = 2*m1Pitch

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

        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=CenterLineGrid(),
                                     spg=EnclosureGrid( pitch=m2Pitch//2, stoppoint=16)))
        self.pl.clg.addCenterLine( 0,            plWidth, False)
        self.pl.clg.addCenterLine( plPitch//2,   plWidth, True)
        self.pl.clg.addCenterLine( plPitch,      plWidth, False)
        self.pl.clg.addCenterLine( 3*plPitch//2, plWidth, True)
        self.pl.clg.addCenterLine( 2*plPitch,      plWidth, False)
        self.pl.clg.semantic()

        self.nd = self.addGen( Region( 'nd', 'ndiff',
                                       h_grid=SingleGrid( pitch=ndPitch),
                                       v_grid=self.pl.clg))

        self.pd = self.addGen( Region( 'pd', 'pdiff',
                                       h_grid=SingleGrid( pitch=pdPitch),
                                       v_grid=self.pl.clg))

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
                                     spg=EnclosureGrid( pitch=self.unitCellHeight, stoppoint=self.unitCellHeight//2-m2Pitch)))


        self.dc = self.addGen( Wire( 'dc', 'diffcon', 'v',
                                     clg=CenterLineGrid(),
                                     spg=EnclosureGrid( pitch=m2Pitch//2, stoppoint=0)))

        self.dc.clg.addCenterLine( 0,            dcWidth, True)
        self.dc.clg.addCenterLine( dcPitch//2,   dcWidth, False)
        self.dc.clg.addCenterLine( dcPitch,      dcWidth, True)
        self.dc.clg.addCenterLine( 3*dcPitch//2, dcWidth, False)
        self.dc.clg.addCenterLine( 2*dcPitch,    dcWidth, True)
        self.dc.clg.semantic()


    def nunit( self, x, y):
        self.pushTr( Transformation( x*self.unitCellWidth, y*self.unitCellHeight))

        h = 2*self.m2PerUnitCell

        self.addRegion( self.nd, None, None, (0, -1), (0*h,  2), (1, 1), (0*h,  6))
        self.addRegion( self.pd, None, None, (0, -1), (1*h, -6), (1, 1), (1*h, -2))

        (ds0,ds1) = ('s', 'd') if x % 2 == 0 else ('d','s')

        self.addWire( self.dc, ds0, None,  (0, 0), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.dc, ds0, None,  (0, 0), (0*h + 8, -1), (0*h + 12, 1))

        self.addWire( self.pl, None, None, (0,-1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, 'g', None,  (0, 1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, 'g', None,  (1,-1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, None, None, (1, 1), (0*h + 2, -1), (0*h + 6,  1))

        self.addWire( self.pl, None, None, (0,-1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, 'g', None,  (0, 1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, 'g', None,  (1,-1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, None, None, (1, 1), (0*h + 8, -1), (0*h + 12, 1))

        self.addWire( self.dc, ds1, None,  (1, 0), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.dc, ds1, None,  (1, 0), (0*h + 8, -1), (0*h + 12, 1))

#        self.addWire( self.pc, 'g', None, (y, 0), (x, 1), ((x+1),-1))

        self.addWire( self.m1, ds0, None, (0, 0), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, 'g', None, (0, 1), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, ds1, None, (1, 0), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))

        assert self.m2PerUnitCell % 2 == 1

        for o in range(0,self.m2PerUnitCell+1):
            self.addWire( self.m2, '_', None, (0, o), (0, -1), (1, 1))

        self.popTr()
