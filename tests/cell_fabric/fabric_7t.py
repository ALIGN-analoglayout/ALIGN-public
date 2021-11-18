from align.cell_fabric import SingleGrid, EnclosureGrid
from align.cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from align.cell_fabric import Canvas as AbstractCanvas
from align.cell_fabric import Wire, Via, Region

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
        for i in range(5):
            self.pl.clg.addCenterLine( i*plPitch//2, plWidth, i % 2 == 1)
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

        for i in range(5):
            self.dc.clg.addCenterLine( i*dcPitch//2, dcWidth, i % 2 == 0)
        self.dc.clg.semantic()

        self.v0 = self.addGen( Via( 'v0', 'via0', v_clg=self.m1.clg, h_clg=self.pc.clg))
        self.v1 = self.addGen( Via( 'v1', 'via1', v_clg=self.m1.clg, h_clg=self.m2.clg))
        self.v2 = self.addGen( Via( 'v2', 'via2', v_clg=self.m3.clg, h_clg=self.m2.clg))

    def nunit( self):
        h = 2*self.m2PerUnitCell

        (ds0, ds1) = ('s', 'd')

        self.addRegion( self.nd, None, (0, -1), (0*h,  2), (1, 1), (0*h,  6))
        self.addRegion( self.pd, None, (0, -1), (1*h, -6), (1, 1), (1*h, -2))

        self.addWire( self.dc, ds0, (0, 0), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.dc, ds0, (0, 0), (0*h + 8, -1), (0*h + 12, 1))

        self.addWire( self.pl, None, (0,-1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, 'g', (0, 1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, 'g', (1,-1), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.pl, None, (1, 1), (0*h + 2, -1), (0*h + 6,  1))

        self.addWire( self.pl, None, (0,-1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, 'g', (0, 1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, 'g', (1,-1), (0*h + 8, -1), (0*h + 12, 1))
        self.addWire( self.pl, None, (1, 1), (0*h + 8, -1), (0*h + 12, 1))

        self.addWire( self.dc, ds1, (1, 0), (0*h + 2, -1), (0*h + 6,  1))
        self.addWire( self.dc, ds1, (1, 0), (0*h + 8, -1), (0*h + 12, 1))

        self.addWire( self.m1, ds0, (0, 0), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, 'g', (0, 1), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))
        self.addWire( self.m1, ds1, (1, 0), (0*self.m2PerUnitCell + 1,-1), (1*self.m2PerUnitCell - 1, 1))

        assert self.m2PerUnitCell % 2 == 1

        for o in range(0,self.m2PerUnitCell+1):
            self.addWire( self.m2, None, (0, o), (0, -1), (1, 1))
