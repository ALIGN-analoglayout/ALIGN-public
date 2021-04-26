from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class TapGenerator(DefaultCanvas):

    def __init__(self, pdk, height, fin, gate, gateDummy, shared_diff):
        super().__init__(pdk)
        self.finsPerUnitCell = height
        assert self.finsPerUnitCell % 4 == 0
        assert (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])%self.pdk['M2']['Pitch']==0
        self.m2PerUnitCell = (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])//self.pdk['M2']['Pitch']
        self.unitCellHeight = self.m2PerUnitCell* self.pdk['M2']['Pitch']
        ######### Derived Parameters ############
        self.shared_diff = shared_diff
        self.gateDummy = gateDummy
        self.gate = 2*gate
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
        
        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        self.fin_diff = self.addGen( Wire( 'fin_diff', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=self.pdk['Poly']['Pitch']))) 
        
        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'Pselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'Nwell',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        stoppoint = unitCellLength//2-self.pdk['Active']['activebWidth_H']//2
        offset_active_body = (self.lFin//2)*self.pdk['Fin']['Pitch']-self.pdk['Fin']['Pitch']//2
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

    def _addTap(self, x_cells, y, yloc=None, name='M1'):
        self._xpins = collections.defaultdict(lambda: collections.defaultdict(list))
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        for x in range(x_cells):
            fullname = f'{name}_X{x}_Y{y}'
            gate_x = self.gateDummy*self.shared_diff + x*gu + gu // 2
            self._xpins[name]['B'].append(gate_x)
            if self.shared_diff == 0:
                self.addWire( self.activeb, None, None, y, (x,1), (x+1,-1)) 
                self.addWire( self.pb, None, None, y, (x,1), (x+1,-1)) 
            else:
                self.addWire( self.activeb_diff, None, None, y, 0, self.gate*x_cells+1)
                self.addWire( self.pb_diff, None, None, y, (x,1), (x+1,-1))
            self.addWire( self.m1, None, None, gate_x, (y*h+self.lFin//4-1, -1), (y*h+self.lFin//4+1, 1))
            self.addVia( self.va, f'{fullname}:B', None, gate_x, y*h+self.lFin//4)
        self.addWireAndViaSet('B', 'B', self.m2, self.v1, y*h+self.lFin//4, self._xpins[name]['B'])

    def addNMOSTap( self, x_cells, y_cells):
        print(y_cells)
        self._addTap(x_cells, (y_cells-1))
        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), -1, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells*self.lFin) 

    def addPMOSTap( self, x_cells, y_cells):

        self._addTap(x_cells, (y_cells-1))

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells*self.lFin)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells*self.lFin)
