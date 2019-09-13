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
        activeWidth =  p['Fin']['Pitch']*fin_u
        activeOffset = p['Fin']['Pitch']*fin//2 + finDummy*p['Fin']['Pitch']-p['Fin']['Pitch']//2
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
        for i in range(max(activeWidth//(2*p['M2']['Pitch']), 1) + ((fin-fin_u)//2 + finDummy+1)//2):
            self.v0.h_clg.addCenterLine((i-1+fin_u//fin)*3*p['Fin']['Pitch'],    p['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['V0']['WidthY'], False)

    def _gen_abstract_MOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy):

        # Draw FEOL Layers
        self.addWire( self.active, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.RVT,    None,    None, y, (x, 1), (x+1, -1))
        self.addWire( self.pc, None, None, y, (x,1), (x+1,-1))
        for i in range(1,  self.finsPerUnitCell):
            self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)
        for i in range(self.gatesPerUnitCell):
            self.addWire( self.pl, None, None, self.gatesPerUnitCell*x+i,   (y,0), (y,1))

        # Source, Drain, Gate Connections

        def _connect_diffusion(x, port):
            self.addWire( self.m1, None, None, x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.LISD, None, None, x, (y, 1), (y+1, -1))
            for j in range((((fin-fin_u)//2 +finDummy+3)//2),self.v0.h_clg.n):
                self.addVia( self.v0, port, None, x, (y, j))

        grid_y0 = y*self.m2PerUnitCell + finDummy//2-1
        grid_y1 = grid_y0+(fin+2)//2
        gate_x = x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, None, gate_x , (grid_y0, -1), (grid_y1, 1))
        self.addVia( self.va, None, None, gate_x, (y*self.m2PerUnitCell//2, 1))
        # Connect Source (gate_x - 1)
        _connect_diffusion(gate_x - 1, None)
        # Connect Drain (gate_x - 1)
        _connect_diffusion(gate_x + 1, None)

    def _gen_routing(self, y, y_cells, Routing):
            for (pin, contact, track, m3route) in Routing:
                self.addWire( self.m2, pin, pin, y*self.m2PerUnitCell+track, (min(contact), -1), (max(contact), 1))
                if y_cells > 1:
                   self.addWire( self.m3, pin, pin, m3route, (track, -1), (y*self.m2PerUnitCell+track, 1))
                   self.addVia( self.v2, None, None, m3route, track)
                   self.addVia( self.v2, None, None, m3route, y*self.m2PerUnitCell+track)

                for i in contact:
                    self.addVia( self.v1, None, None, i, y*self.m2PerUnitCell+track)

    def genNMOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        self._gen_abstract_MOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy)

        if x == x_cells -1:
            self._gen_routing(y, y_cells, Routing)

        #####   Nselect Placement   #####
        if x == x_cells -1 and y == y_cells -1:
            self.addRegion( self.nselect, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)

    def genPMOS( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        self._gen_abstract_MOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy)

        if x == x_cells -1:
            self._gen_routing(y, y_cells, Routing)

        #####   Pselect and Nwell Placement   #####
        if x == x_cells -1 and y == y_cells -1:
            self.addRegion( self.pselect, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)
            self.addRegion( self.nwell, None, None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)* self.finsPerUnitCell)
