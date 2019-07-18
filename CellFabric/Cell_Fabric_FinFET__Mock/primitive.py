from cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid


class CanvasNMOS(DefaultCanvas):
    def __init__( self, fin_u, fin, finDummy, gate, gateDummy,
                  pdkfile='../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json'):
        p = Pdk().load(pdkfile)
        super().__init__(p)
        assert   p['Feol']['v0Pitch'] < 2*p['M2']['Pitch']

######### Derived Parameters ############
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy
       # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        assert fin >= fin_u, "number of fins in the transistor is greater than unit cell fins" 
        assert fin_u > 3, "number of fins in the transistor must be more than 2"
        assert finDummy % 2 == 0
        assert gateDummy > 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell* p['M2']['Pitch']
        unitCellLength = self.gatesPerUnitCell* p['Poly']['Pitch'] 
        activeWidth1 =  p['Fin']['Pitch']*fin_u
        activeWidth =  p['Fin']['Pitch']*fin
        activeOffset = activeWidth//2 + finDummy*p['Fin']['Pitch']-p['Fin']['Pitch']//2
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth1 + 2*p['Feol']['active_enclosure']
  
        self.m0 = self.addGen( Wire( 'm0', 'M0', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   p['Feol']['m0Pitch'], width= p['Feol']['m0Width'], offset= p['Feol']['m0Pitch']//2),
                                     spg=EnclosureGrid( pitch=activePitch, offset=activeOffset, stoppoint=activeWidth//2, check=True)))

        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= p['Poly']['Pitch'], width= p['Poly']['Width'], offset= p['Poly']['Offset']),
                                     spg=SingleGrid( offset= p['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Fin']['Width'], offset= p['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        stoppoint = (gateDummy-1)* p['Poly']['Pitch'] +  p['Poly']['Offset']
        self.active = self.addGen( Wire( 'active', 'active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth1, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
        
        
        self.RVT = self.addGen( Wire( 'RVT', 'polycon', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
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

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg))

        self.v0.h_clg.addCenterLine( 0,                 p['V0']['WidthY'], False)
        for i in range(max(activeWidth1//(2*p['M2']['Pitch']), 1) + ((fin-fin_u)//2 + finDummy+1)//2):
            self.v0.h_clg.addCenterLine((i-1+fin_u//fin)*p['Feol']['v0Pitch'],    p['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['V0']['WidthY'], False)



        

