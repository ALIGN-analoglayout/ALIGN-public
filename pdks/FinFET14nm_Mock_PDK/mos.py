from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric.generators import *
from align.cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class MOSGenerator(DefaultCanvas):

    def __init__(self, pdk, height, fin, gate, gateDummy, shared_diff, stack):
        super().__init__(pdk)
        self.finsPerUnitCell = height
        self.m2PerUnitCell = (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])//self.pdk['M2']['Pitch']
        self.unitCellHeight = self.m2PerUnitCell* self.pdk['M2']['Pitch']
        ######### Derived Parameters ############
        self.shared_diff = shared_diff
        self.stack = stack
        self.gateDummy = gateDummy
        self.gate = (2*gate)*self.stack
        self.gatesPerUnitCell = self.gate + 2*self.gateDummy*(1-self.shared_diff)
        self.finDummy = (self.finsPerUnitCell-fin)//2
        self.lFin = height ### This defines numebr of fins for tap cells; Should we define it in the layers.json?
        assert self.finDummy >= 8, "number of fins in the transistor must be less than height"
        assert fin > 3, "number of fins in the transistor must be more than 2"
        assert fin % 2 == 0, "number of fins in the transistor must be even" 
        assert gateDummy > 0
        unitCellLength = self.gatesPerUnitCell* self.pdk['Poly']['Pitch']
        activeOffset = self.unitCellHeight//2 -self.pdk['Fin']['Pitch']//2
        activeWidth =  self.pdk['Fin']['Pitch']*fin
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*self.pdk['Active']['active_enclosure']

        self.pl = self.addGen( Wire( 'pl', 'Poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= self.pdk['Poly']['Pitch'], width= self.pdk['Poly']['Width'], offset= self.pdk['Poly']['Offset']),
                                     spg=SingleGrid( offset= self.pdk['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        self.fin_diff = self.addGen( Wire( 'fin_diff', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=self.pdk['Poly']['Pitch']))) 

        stoppoint = ((self.gateDummy-1)* self.pdk['Poly']['Pitch'] +  self.pdk['Poly']['Offset'])*(1-self.shared_diff)
        self.active = self.addGen( Wire( 'active', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Wire( 'RVT', 'Rvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
        
        self.LVT = self.addGen( Wire( 'LVT', 'Lvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.HVT = self.addGen( Wire( 'HVT', 'Hvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.SLVT = self.addGen( Wire( 'SLVT', 'Slvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = activeOffset-activeWidth//2
        self.LISD = self.addGen( Wire( 'LISD', 'Lisd', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M1']['Pitch'], width=self.pdk['Lisd']['LisdWidth'], offset=self.pdk['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))

        offset = self.gateDummy*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Offset'] - self.pdk['Poly']['Pitch']//2
        stoppoint = self.gateDummy*self.pdk['Poly']['Pitch'] + self.pdk['Poly']['Offset']-self.pdk['Pc']['PcExt']-self.pdk['Poly']['Width']//2
        self.pc = self.addGen( Wire( 'pc', 'Pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M2']['Pitch'], width=self.pdk['Pc']['PcWidth'], offset=self.pdk['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=offset*self.shared_diff, stoppoint=stoppoint-offset*self.shared_diff, check=True)))

        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'Pselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'Nwell',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        self.active_diff = self.addGen( Wire( 'active_diff', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
        
        self.RVT_diff = self.addGen( Wire( 'RVT_diff', 'Rvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2))) 

        self.LVT_diff = self.addGen( Wire( 'LVT_diff', 'Lvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
   
        self.HVT_diff = self.addGen( Wire( 'HVT_diff', 'Hvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
        
        self.SLVT_diff = self.addGen( Wire( 'SLVT_diff', 'Slvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))

        stoppoint = unitCellLength//2-self.pdk['Active']['activebWidth_H']//2
        offset_active_body = (self.lFin//2)*self.pdk['Fin']['Pitch']+self.unitCellHeight-self.pdk['Fin']['Pitch']//2
        self.activeb = self.addGen( Wire( 'activeb', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Active']['activebWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
         
        self.activeb_diff = self.addGen( Wire( 'activeb_diff', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Active']['activebWidth'], offset=offset_active_body),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))

        self.pb_diff = self.addGen( Wire( 'pb_diff', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2))) 

        stoppoint = unitCellLength//2-self.pdk['Pb']['pbWidth_H']//2
        self.pb = self.addGen( Wire( 'pb', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.LISDb = self.addGen( Wire( 'LISDb', 'Lisd', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   self.pdk['M1']['Pitch'], width= self.pdk['Lisd']['LisdWidth'], offset= self.pdk['M1']['Offset']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], offset=0, stoppoint= self.pdk['M2']['Width']//2+self.pdk['V1']['VencA_L'], check=True)))

        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY']))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY']))

        self.v0.h_clg.addCenterLine( 0,                 self.pdk['V0']['WidthY'], False)
        v0pitch = 3*self.pdk['Fin']['Pitch']
        v0Offset = ((self.finDummy+3)//2)*self.pdk['M2']['Pitch'] 
        for i in range((activeWidth-2*self.pdk['M2']['Pitch']) // v0pitch + 1):
            self.v0.h_clg.addCenterLine(i*v0pitch+v0Offset,    self.pdk['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    self.pdk['V0']['WidthY'], False)
        info = self.pdk['V0']

    def _addMOS( self, x, y, x_cells,  vt_type, name='M1', reflect=False, **parameters):

        fullname = f'{name}_X{x}_Y{y}'
        self.subinsts[fullname].parameters.update(parameters)

        def _connect_diffusion(i, pin):
            self.addWire( self.m1, None, i, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.LISD, None, i, (y, 1), (y+1, -1))
            for j in range(1,self.v0.h_clg.n): ## self.v0.h_clg.n??
                self.addVia( self.v0, f'{fullname}:{pin}', i, (y, j))
            self._xpins[name][pin].append(i)
            
        # Draw FEOL Layers
        if self.shared_diff == 0:
            self.addWire( self.active, None, y, (x,1), (x+1,-1)) 
        elif self.shared_diff == 1 and x == x_cells-1:
            self.addWire( self.active_diff, None, y, 0, self.gate*x_cells+1)
        else:
            pass

        for i in range(self.gatesPerUnitCell):
            self.addWire( self.pl, None, self.gatesPerUnitCell*x+self.gateDummy*self.shared_diff+i,   (y,0), (y,1))

        if self.shared_diff == 1 and (x == 0 or x == x_cells-1):
            dummy_gates = self.gatesPerUnitCell*x_cells+self.gateDummy if x == x_cells-1 else 0
            for i in range(self.gateDummy):
                self.addWire( self.pl, None, dummy_gates+i,   (y,0), (y,1))

        if self.shared_diff == 1:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin_diff, None, self.finsPerUnitCell*y+i, 0, (self.gate*x_cells+2*self.gateDummy))
        else:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin, None, self.finsPerUnitCell*y+i, x, x+1) 

        def _addRVT(x, y, x_cells):
            if self.shared_diff == 0:
                self.addWire( self.RVT,  None, y,          (x, 1), (x+1, -1))
            elif self.shared_diff == 1 and x == x_cells-1:
                self.addWire( self.RVT_diff,  None, y, 0, self.gate*x_cells+1)
            else:
                pass
    
        def _addLVT(x, y, x_cells):
            if self.shared_diff == 0:
                self.addWire( self.LVT,  None, y,          (x, 1), (x+1, -1))
            elif self.shared_diff == 1 and x == x_cells-1:
                self.addWire( self.LVT_diff,  None, y, 0, self.gate*x_cells+1)
            else:
                pass
    
        def _addHVT(x, y, x_cells):
            if self.shared_diff == 0:
                self.addWire( self.HVT,  None, y,          (x, 1), (x+1, -1))
            elif self.shared_diff == 1 and x == x_cells-1:
                self.addWire( self.HVT_diff,  None, y, 0, self.gate*x_cells+1)
            else:
                pass

        def _addSLVT(x, y, x_cells):
            if self.shared_diff == 0:
                self.addWire( self.SLVT,  None, y,          (x, 1), (x+1, -1))
            elif self.shared_diff == 1 and x == x_cells-1:
                self.addWire( self.SLVT_diff,  None, y, 0, self.gate*x_cells+1)
            else:
                pass  
     
        if vt_type == 'RVT':
            _addRVT(x, y, x_cells)
        elif vt_type == 'LVT':
            _addLVT(x, y, x_cells)
        elif vt_type == 'HVT':
            _addHVT(x, y, x_cells)
        elif vt_type == 'SLVT':
            _addSLVT(x, y, x_cells)
        else:
            print("This VT type not supported")
            exit()

        # Source, Drain, Gate Connections
        grid_y0 = y*self.m2PerUnitCell + 1
        grid_y1 = (y+1)*self.m2PerUnitCell-5
        gate_x = self.gateDummy*self.shared_diff + x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, gate_x , (grid_y1+2, -1), (grid_y1+4, 1))
        self.addWire( self.pc, None, grid_y1+1, (x,1), (x+1,-1))
        self.addVia( self.va, f'{fullname}:G', gate_x, grid_y1+2)
        self._xpins[name]['G'].append(gate_x)

        # Connect Source & Drain
        (center_terminal, side_terminal) = ('S', 'D') if self.gate%4 == 0 else ('D', 'S')
        center_terminal = 'D' if self.stack > 1 else center_terminal # for stacked devices
        _connect_diffusion(gate_x, center_terminal)

        for x_terminal in range(1,1+self.gate//2):
            terminal = center_terminal if x_terminal%2 == 0 else side_terminal #for fingers
            if self.stack > 1 and x_terminal != self.gate//2: continue
            terminal = 'S' if self.stack > 1 else terminal 
            if reflect:
                _connect_diffusion(gate_x - x_terminal, terminal)
                _connect_diffusion(gate_x + x_terminal, terminal)
            else:
                _connect_diffusion(gate_x - x_terminal, terminal)
                _connect_diffusion(gate_x + x_terminal, terminal)

    def _addBodyContact(self, x, y, x_cells, yloc=None, name='M1'):
        fullname = f'{name}_X{x}_Y{y}'
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = self.gateDummy*self.shared_diff + x*gu + gu // 2
        self._xpins[name]['B'].append(gate_x)
        self.addWire( self.m1, None, gate_x, ((y+1)*h+self.lFin//4-1, -1), ((y+1)*h+self.lFin//4+1, 1))
        self.addWire( self.LISDb, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        self.addVia( self.va, f'{fullname}:B', gate_x, (y+1)*h + self.lFin//4)

        if self.shared_diff == 0:
            self.addWire( self.activeb, None, y, (x,1), (x+1,-1)) 
            self.addWire( self.pb, None, y, (x,1), (x+1,-1))
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin, None, self.finsPerUnitCell*y+i, x, x+1)
        else:
            self.addWire( self.activeb_diff, None, y, 0, self.gate*x_cells+1)
            self.addWire( self.pb_diff, None, y, (x,1), (x+1,-1))
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin_diff, None, self.finsPerUnitCell*y+i, 0, (self.gate*x_cells+2*self.gateDummy))
 
