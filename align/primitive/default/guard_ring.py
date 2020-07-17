from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class RingGenerator(DefaultCanvas):

    def __init__(self, pdk):
        super().__init__(pdk)

        ######### Derived Parameters ########

        self.ring_enclosure = self.pdk['GuardRing']['activeRing_enclosure']/self.pdk['M2']['Pitch']
        self.ring_width = self.pdk['GuardRing']['activeRingWidth']/self.pdk['M2']['Pitch']
                
        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect_ring = self.addGen( Region( 'pselect_ring', 'Pselect',
                                            v_grid=self.pdk['M2']['Pitch'],
                                            h_grid=self.pdk['M2']['Pitch']))

        self.active_ring = self.addGen( Region( 'active_ring', 'Active',
                                            v_grid=self.pdk['M2']['Pitch'],
                                            h_grid=self.pdk['M2']['Pitch']))

        self.m1_ring = self.addGen( Region( 'M1_ring', 'M1',
                                            v_grid=self.pdk['M2']['Pitch'],
                                            h_grid=self.pdk['M2']['Pitch']))

        #self.nwell = self.addGen( Region( 'nwell', 'Nwell',
        #                                    v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
         
        
        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY']))

        
    def addRing( self, x_length, y_length):
        assert x_length == 1 or y_length == 1
        x_cells = x_length/self.pdk['M2']['Pitch']
        y_cells = y_length/self.pdk['M2']['Pitch']
        x_cells = self.ring_width if x_length == 1 else x_length
        y_cells = self.ring_width if y_length == 1 else y_length
        #self.addWire( self.m1_ring, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.lFin)
        #self.addVia( self.va, None, None, gate_x, grid_y1+2)
        #self.addVia( self.va, f'{fullname}:G', None, gate_x, grid_y1+2)

        self.addWire( self.m1_ring, self.ring_enclosure, self.ring_enclosure, (x_cells+self.ring_enclosure), (y_cells+self.ring_enclosure))

        self.addWire( self.active_ring, self.ring_enclosure, self.ring_enclosure, (x_cells+self.ring_enclosure), (y_cells+self.ring_enclosure))

        self.addRegion( self.pselect_ring, None, None, 0, 0, (x_cells+2*self.ring_enclosure), (y_cells+2*self.ring_enclosure))

        #self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.lFin)

        
