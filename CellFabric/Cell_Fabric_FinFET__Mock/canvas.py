from cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / '../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json').resolve()

class FinFET_Mock_PDK_Canvas(DefaultCanvas):

    def __init__( self, fin_u, fin, finDummy, gate, gateDummy,
                  pdkfile=pdkfile):

        p = Pdk().load(pdkfile)
        super().__init__(p)
        assert   3*p['Fin']['Pitch'] < 2*p['M2']['Pitch']

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
        PcLength = (gate-1)*p['Poly']['Pitch']+p['Poly']['Width']+2*p['Feol']['PcExt']
  
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
        
        stoppoint = activeOffset-activeWidth1//2
        self.LISD = self.addGen( Wire( 'LISD', 'lisd', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=p['LISD']['Pitch'], width=p['LISD']['Width'], offset=p['LISD']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))
 
        stoppoint = gateDummy*p['Poly']['Pitch']+p['Poly']['Offset']-p['Feol']['PcExt']-p['Poly']['Width']//2      
        self.pc = self.addGen( Wire( 'pc', 'pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Feol']['pcWidth'], offset=p['M2']['Pitch']),
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
        for i in range(max(activeWidth1//(2*p['M2']['Pitch']), 1) + ((fin-fin_u)//2 + finDummy+1)//2):
            self.v0.h_clg.addCenterLine((i-1+fin_u//fin)*3*p['Fin']['Pitch'],    p['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['V0']['WidthY'], False)

    def _gen_abstract_MOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        (SA, GA, DA, SB, GB, DB) = SDG
        (S, D, G) = (SA+SB, DA+DB, GA+GB)
        #####   This part generats locations of S/D/G   #####
        gu = self.gatesPerUnitCell
        h = self.m2PerUnitCell
                       
        self.addWire( self.active, None, None, y, (x,1), (x+1,-1)) 
        self.addWire( self.RVT,    None,    None, y, (x, 1), (x+1, -1))
        self.addWire( self.pc, None, None, y, (x,1), (x+1,-1))
 
 
        for i in range(1,  self.finsPerUnitCell):
            self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)

        #####   Gate Placement   #####                       
        for i in range(gu):        
            self.addWire( self.pl, None, None, gu*x+i,   (y,0), (y,1))

        if x_cells-1==x:
            grid_y0 = y*h + finDummy//2-1
            grid_y1 = grid_y0+(fin+2)//2
            for i in G:
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
                self.addVia( self.va, None, None, i, (y*h//2, 3))
            for i in S+D:
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
                self.addWire( self.LISD, None, None, i, (y, 1), (y+1, -1)) 
                for j in range((((fin-fin_u)//2 +finDummy+3)//2),self.v0.h_clg.n):
                    self.addVia( self.v0, None, None, i, (y, j))

            #pin = 'VDD' if y%2==0 else 'GND'    
            #self.addWire( self.m2, pin, pin, h*(y+1), (0, 1), (x_cells*gu, -1))
            #self.addWire( self.m2, 'GND', 'GND', 0, (0, 1), (x_cells*gu, -1))                   
            for (pin, contact, track, m3route) in Routing:
                self.addWire( self.m2, pin, pin, y*h+track, (min(contact), -1), (max(contact), 1))
                if y_cells > 1:
                   self.addWire( self.m3, pin, pin, m3route, (track, -1), (y*h+track, 1))
                   self.addVia( self.v2, None, None, m3route, track)
                   self.addVia( self.v2, None, None, m3route, y*h+track)

                for i in contact:
                    self.addVia( self.v1, None, None, i, y*h+track) 

    def genNMOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):
        
        self._gen_abstract_MOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

        #####   Nselect Placement   #####
        if x == x_cells -1 and y == y_cells -1:
            self.addRegion( self.nselect, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)

    def genPMOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        self._gen_abstract_MOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

        #####   Pselect and Nwell Placement   #####
        if x == x_cells -1 and y == y_cells -1:      
            self.addRegion( self.pselect, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)
            self.addRegion( self.nwell, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)    
