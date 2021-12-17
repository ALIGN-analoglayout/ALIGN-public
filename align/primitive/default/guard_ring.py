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

        self.WidthX = self.pdk['M1']['Width'] + ((self.pdk['GuardRing']['viaArray']+1)*self.pdk['M1']['Pitch'])
        self.WidthY = self.pdk['M1']['Width'] + ((self.pdk['GuardRing']['viaArray']+1)*self.pdk['M1']['Pitch'])

        self.ring_enclosureX = math.ceil(self.pdk['GuardRing']['activeRing_enclosure']/self.pdk['M1']['Pitch'])

        self.ring_enclosureY = math.ceil(self.pdk['GuardRing']['activeRing_enclosure']/self.pdk['M2']['Pitch'])

        #### Layers definition ####

        self.m1_ring = self.addGen(Wire('m_test', 'M1', 'v',
                                        clg=UncoloredCenterLineGrid(pitch=self.WidthX, width=self.WidthX),
                                        spg=EnclosureGrid(pitch=self.pdk['M2']['Pitch'], stoppoint=0, check=False)))

        self.pselect_ring = self.addGen(Region('pselect_ring', 'Pselect',
                                               v_grid=self.m1.clg,
                                               h_grid=self.m2.clg))

        self.active_ring = self.addGen(Region('active_ring', 'Active',
                                              v_grid=UncoloredCenterLineGrid(offset=-self.WidthX//2, pitch=self.WidthX, width=self.WidthX),
                                              h_grid=self.m2.clg))

        # self.nwell = self.addGen( Region( 'nwell', 'Nwell',
        #                                    v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
        #                                    h_grid=self.fin.clg))

        self.va = self.addGen(Via('va', 'V0',
                                  h_clg=self.m2.clg,
                                  v_clg=self.m1_ring.clg,
                                  WidthX=self.WidthX-self.pdk['M1']['Pitch'],
                                  WidthY=self.pdk['V0']['WidthY']))

    def addRing(self, x_cells, y_cells):

        gridX = math.ceil(self.WidthX/self.pdk['M1']['Pitch'])
        gridY = math.ceil(self.WidthY/self.pdk['M2']['Pitch'])

        i = gridX//2+self.ring_enclosureX
        self.addWire(self.m1_ring, 'Body', 0, (self.ring_enclosureY, -1), (gridY+self.ring_enclosureY, -1), netType="pin")
        for j in range(self.ring_enclosureY+1, gridY+self.ring_enclosureY):
            self.addVia(self.va, 'Body', 0, j)

        self.addRegion(self.active_ring, None, 0, self.ring_enclosureY, 1, (gridY+self.ring_enclosureY))

        self.addRegion(self.pselect_ring, None, -(gridX//2+self.ring_enclosureX),
                       0, (gridX//2+self.ring_enclosureX), (gridY+2*self.ring_enclosureY))
