from cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / 'layers.json').resolve()

class FinFET14nm_Mock_PDK_Canvas(DefaultCanvas):

    def __init__( self, fin, finDummy, gate, gateDummy,
                  pdkfile=pdkfile):

        p = Pdk().load(pdkfile)
        super().__init__(p)
        assert   3*p['Fin']['Pitch'] < 2*p['M2']['Pitch']

######### Derived Parameters ############
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy
        self.finDummy = finDummy
       # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        assert fin > 3, "number of fins in the transistor must be more than 2"
        assert finDummy % 2 == 0
        assert gateDummy > 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell* p['M2']['Pitch']
        unitCellLength = self.gatesPerUnitCell* p['Poly']['Pitch']
        activeWidth =  p['Fin']['Pitch']*fin
        activeOffset = activeWidth//2 + finDummy*p['Fin']['Pitch']-p['Fin']['Pitch']//2
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*p['Feol']['active_enclosure']

        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= p['Poly']['Pitch'], width= p['Poly']['Width'], offset= p['Poly']['Offset']),
                                     spg=SingleGrid( offset= p['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Fin']['Width'], offset= p['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        stoppoint = (gateDummy-1)* p['Poly']['Pitch'] +  p['Poly']['Offset']
        self.active = self.addGen( Wire( 'active', 'active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Wire( 'RVT', 'polycon', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = activeOffset-activeWidth//2
        self.LISD = self.addGen( Wire( 'LISD', 'LISD', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=p['M1']['Pitch'], width=p['Feol']['LISDWidth'], offset=p['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = gateDummy*p['Poly']['Pitch']+p['Poly']['Offset']-p['Feol']['PcExt']-p['Poly']['Width']//2
        self.pc = self.addGen( Wire( 'pc', 'pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Feol']['PcWidth'], offset=p['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.nselect = self.addGen( Region( 'nselect', 'nselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'pselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'nwell',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg))

        self.v0.h_clg.addCenterLine( 0,                 p['V0']['WidthY'], False)
        v0pitch = activeWidth//(2*p['M2']['Pitch']) * p['Fin']['Pitch']
        for i in range(activeWidth // v0pitch + 1):
            self.v0.h_clg.addCenterLine(i*v0pitch,    p['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['V0']['WidthY'], False)

