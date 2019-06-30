from cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid


class CanvasNMOS(DefaultCanvas):    
    def __init__( self, fin_u, fin, finDummy, gate, gateDummy):
        p = Pdk().load('../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json') 
        super().__init__(p)                                           
        assert   p['Feol']['v0Pitch'] < 2*p['M2']['Pitch']

######### Derived Parameters ############        
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy
        # Must be a multiple of 2
        assert self.finsPerUnitCell % 2 == 0
        assert finDummy % 2 == 0
        assert gateDummy > 0
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell* p['M2']['Pitch']
        unitCellLength = self.gatesPerUnitCell* p['Poly']['Pitch']
        #dcPitch  = 2* p['M1']['Pitch']               
        #pcPitch  = self.unitCellHeight//2
        #activeWidth1 =  p['Fin']['Pitch']*fin_u
        activeWidth =  p['Fin']['Pitch']*fin
        activeWidth_h = ((gate-1)* p['Poly']['Pitch']) + (p['Feol']['plActive_s']*2)+p['Poly']['Width']
        activeOffset = activeWidth//2 + finDummy* p['Fin']['Pitch']-p['M2']['Pitch']//2+p['Fin']['Offset']
        activePitch = self.unitCellHeight
        RVTPitch = activePitch
        RVTWidth = activeWidth + 2*p['Feol']['active_enclosure']
        RVTOffset = RVTWidth//2 + finDummy* p['Fin']['Pitch']-p['Fin']['Pitch']//2-p['Feol']['active_enclosure']+p['Fin']['Offset']

############Include these all ###########
       # self.extension_x = (self. self.pitch('Poly', 0, p) - self. p['Poly']['Width'])//2  ### Minimum horizontal extension of GCUT past GATE

        self.m0 = self.addGen( Wire( 'm0', 'M0', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   p['Feol']['m0Pitch'], width= p['Feol']['m0Width'], offset= p['Feol']['m0Pitch']//2),
                                     spg=EnclosureGrid( pitch=activePitch, offset=activeOffset, stoppoint=activeWidth//2, check=True)))

        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= p['Poly']['Pitch'], width= p['Poly']['Width'], offset= p['Poly']['Offset']),
                                     spg=SingleGrid( offset= p['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Fin']['Width'], offset= p['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        self.active = self.addGen( Wire( 'active', 'active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=CenterLineGrid()))
        stoppoint = (gateDummy-1)* p['Poly']['Pitch'] +  p['Poly']['Offset']
        self.active.spg.addCenterLine( 0,         activeWidth_h, False)       
        self.active.spg.addCenterLine( stoppoint, activeWidth_h,        True)
        self.active.spg.addCenterLine( unitCellLength-stoppoint, activeWidth_h,         True)
        self.active.spg.addCenterLine( unitCellLength, activeWidth_h,         False)

        self.RVT = self.addGen( Wire( 'RVT', 'polycon', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=RVTPitch, width=RVTWidth, offset=RVTOffset),
                                      spg=CenterLineGrid()))

        self.RVT.spg.addCenterLine( 0,         activeWidth_h, False)       
        self.RVT.spg.addCenterLine( stoppoint, activeWidth_h,        True)
        self.RVT.spg.addCenterLine( unitCellLength-stoppoint, activeWidth_h,         True)
        self.RVT.spg.addCenterLine( unitCellLength, activeWidth_h,         False)

        self.nselect = self.addGen( Region( 'nselect', 'nselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'pselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'nwell',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        v0x_offset =  p['M2']['Offset'] + (1+finDummy//2)* p['M2']['Pitch']
        #print( "SMB",   p['Feol']['v0Pitch'],  self.pitch('M2', 0, p))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg))

        self.v0.h_clg.addCenterLine( 0,                 p['Feol']['v0Width'], False)       
        for i in range(activeWidth//(2* p['M2']['Pitch'])):
            self.v0.h_clg.addCenterLine( v0x_offset+i*  p['Feol']['v0Pitch'],    p['Feol']['v0Width'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['Feol']['v0Width'], False)


        

