import math
from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class RingGenerator(DefaultCanvas):

    def __init__(self, pdk):
        super().__init__(pdk)

        ######### Derived Parameters ########
 
        self.WidthX = self.pdk['GuardRing']['viaArray']*(self.pdk['V0']['SpaceX']+self.pdk['V0']['WidthX'])
        self.WidthY = (self.pdk['GuardRing']['viaArray']+1)*(self.pdk['V0']['SpaceX']+self.pdk['V0']['WidthX']+1)
        self.ring_enclosureX = math.ceil(self.pdk['GuardRing']['activeRing_enclosure']/self.pdk['M1']['Pitch'])
        
        self.ring_enclosureY = math.ceil(self.pdk['GuardRing']['activeRing_enclosure']/self.pdk['M2']['Pitch'])
        
        m1_ring_WidthX = math.ceil(self.WidthX/self.pdk['M1']['Pitch'])*self.pdk['M1']['Pitch']
        m1_ring_WidthY = math.ceil(self.WidthX/self.pdk['M2']['Pitch'])*self.pdk['M2']['Pitch']
        #### Layers definition ####

        self.m1_ring = self.addGen( Wire( 'm_test', 'M1', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=self.pdk['M1']['Pitch'], width=self.pdk['M1']['Pitch']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], stoppoint=0, check=False)))

        self.pselect_ring = self.addGen( Region( 'pselect_ring', 'Pselect',
                                            v_grid=self.m1.clg,
                                            h_grid=self.m2.clg))

        self.active_ring = self.addGen( Region( 'active_ring', 'Active',
                                            v_grid=UncoloredCenterLineGrid( offset=-self.pdk['M1']['Pitch']//2, pitch=self.pdk['M1']['Pitch'], width=self.pdk['M1']['Pitch']),
                                            h_grid=self.m2.clg))

 
        #self.nwell = self.addGen( Region( 'nwell', 'Nwell',
        #                                    v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
        #                                    h_grid=self.fin.clg))
        
        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY'])) 
        
    def addRing( self, x_cells, y_cells):

        gridX = math.ceil(self.WidthX/self.pdk['M1']['Pitch'])
        gridY = math.ceil(self.WidthY/self.pdk['M2']['Pitch'])

        for i in range(self.ring_enclosureX, gridX+self.ring_enclosureX):
            self.addWire( self.m1_ring, None, None, i, (self.ring_enclosureY, -1), (gridY+self.ring_enclosureY, -1))
            for j in range(self.ring_enclosureY+1, gridY+self.ring_enclosureY): 
                self.addVia( self.va, None, None, i, j)
        #self.addWire( self.m2, None, None, 1, (1, -1), (5, -1))
        #
        self.addRegion( self.active_ring, None, None, self.ring_enclosureX, self.ring_enclosureY, (gridX+self.ring_enclosureX), (gridY+self.ring_enclosureY))

        self.addRegion( self.pselect_ring, None, None, 0, 0, (gridX+2*self.ring_enclosureX), (gridY+2*self.ring_enclosureY))

        #self.addRegion( self.boundary, 'Boundary', None, 0, 0, (gridX+2*self.ring_enclosureX), (gridY+2*self.ring_enclosureY))




        
