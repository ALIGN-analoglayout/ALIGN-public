from cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid
from cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / 'layers.json').resolve()

class FinFETCanvas(DefaultCanvas):
    def __init__( self, fin_u, fin, finDummy, gate, gateDummy,
                  pdkfile=pdkfile):
        p = Pdk().load(pdkfile)
        super().__init__(p)
        #assert   3*p['Fin']['Pitch'] < 2*p['M2']['Pitch']
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
        pcLength = (gate-1)*p['Poly']['Pitch']+p['Poly']['Width']+2*p['Feol']['pcGateExt']
     
        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= p['Poly']['Pitch'], width= p['Poly']['Width'], offset= p['Poly']['Offset']),
                                     spg=SingleGrid( offset= p['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Fin']['Width'], offset= p['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        stoppoint = gateDummy*p['Poly']['Pitch']+p['Poly']['Offset']-p['Feol']['plActiveEnc']-p['Poly']['Width']//2
        self.active = self.addGen( Wire( 'active', 'active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth1, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
        
        stoppoint = gateDummy*p['Poly']['Pitch']+p['Poly']['Offset']-p['Feol']['pcGateExt']-p['Poly']['Width']//2      
        self.pc = self.addGen( Wire( 'pc', 'pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Feol']['pcWidth'], offset=p['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = activeOffset-activeWidth1//2
        self.lisd = self.addGen( Wire( 'lisd', 'lisd', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=p['M1']['Pitch'], width=p['Feol']['lisdWidth'], offset=p['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))
        

        self.sdt = self.addGen( Wire( 'sdt', 'sdt', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=p['M1']['Pitch'], width=p['Feol']['lisdWidth'], offset=p['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))
        
        
        self.gcut = self.addGen( Wire( 'gcut', 'gcut', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Feol']['gcutWidth'], offset= p['Fin']['Offset']+p['Feol']['gcutWidth']//2),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))
        self.gcut1 = self.addGen( Wire( 'gcut1', 'gcut', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Feol']['gcutWidth'], offset= p['Fin']['Offset']-p['Feol']['gcutWidth']//2),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

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

        self.v0.h_clg.addCenterLine( 0,                 p['Feol']['v0Width'], False)       
        for i in range(activeWidth1//(p['M2']['Pitch'])+ ((fin-fin_u)//2 + finDummy+1)//2):
            self.v0.h_clg.addCenterLine(i*p['Feol']['v0Pitch'],    p['Feol']['v0Width'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['Feol']['v0Width'], False)


class AbstractMOS(FinFETCanvas):

    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):
        (SA, GA, DA, SB, GB, DB) = SDG
        (S, D, G) = (SA+SB, DA+DB, GA+GB)
        

        gu = self.gatesPerUnitCell
        #fin = self.finsPerUnitCell
        h = self.m2PerUnitCell
                       
        self.addWire( self.active, None, None, y, (x,1), (x+1,-1)) 
        self.addWire( self.pc, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.gcut, None, None, self.finsPerUnitCell*y, x, x+1)
        self.addWire( self.gcut1, None, None, self.finsPerUnitCell*(y+1), x, x+1)

        ##### Fin Placement   #####
        for i in range(1, self.finsPerUnitCell):
            self.addWire( self.fin, None, None, self.finsPerUnitCell*y+i, x, x+1)
        
        #####   Gate Placement   #####                       
        for i in range(gu):        
            self.addWire( self.pl, None, None, gu*x+i,   (y,0), (y,1))                
                
        if x_cells-1==x:
            grid_y0 = y*h + finDummy//2-1
            grid_y1 = grid_y0+(fin+2)//2
            for i in G:
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
                self.addVia( self.v0, None, None, i, (y, 2))
            for i in S+D:
                #SD = 'S' if i in S else 'D'
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1)) 
                self.addWire( self.lisd, None, None, i, (y, 1), (y+1, -1))
                self.addWire( self.sdt, None, None, i, (y, 1), (y+1, -1))
                for j in range((((fin-fin_u)//2 +finDummy+3)//2),self.v0.h_clg.n):
                    self.addVia( self.v0, None, None, i, (y, j))

            #pin = 'VDD' if y%2==0 else 'GND'    
            #self.addWire( self.m2, pin, pin, h*(y+1), (0, 1), (x_cells*gu, -1))
            #self.addWire( self.m2, 'GND', 'GND', 0, (0, 1), (x_cells*gu, -1)) 
            track_no = 2                  
            for (pin, contact, track, m3route) in Routing:
                for k in range(track):
                    trackp = track_no + k
                    self.addWire( self.m2,pin, pin, y*h+trackp, (min(contact), -1), (max(contact), 1))
                    self.addVia( self.v2,None, None, m3route, trackp)
                    self.addVia( self.v2,None, None, m3route, y*h+trackp)
                    for i in contact:
                        self.addVia( self.v1, None, None, i, y*h+trackp)
                if y_cells == 1:
                    self.addWire( self.m3,pin, pin, m3route, (2, -1), (h-2, 1))
                else:
                    self.addWire( self.m3,pin, pin, m3route, (track_no, -1), (y*h+trackp, 1))
                track_no = track_no + track 


                   
            
                                                           
