from canvas import Bulk65nm_Mock_PDK_Canvas
from align.cell_fabric import DefaultPrimitiveGenerator

import logging
logger = logging.getLogger(__name__)

class PrimitiveGenerator(Bulk65nm_Mock_PDK_Canvas, DefaultPrimitiveGenerator):

    def _addMOS( self, x, y, name='M1', reflect=False, **parameters):

        # Draw default layers
        #super()._addMOS(x, y, name, reflect, **parameters)
        fullname = f'{name}_X{x}_Y{y}'
        self.subinsts[fullname].parameters.update(parameters)

        def _connect_diffusion(i, pin):
            self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
            for j in range(((self.finDummy+3)//2), self.v0.h_clg.n):
                self.addVia( self.v0, f'{fullname}:{pin}', None, i, (y, j))
            self._xpins[name][pin].append(i)

        # Draw FEOL Layers

        self.addWire( self.active, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.pc, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.RVT,  None, None, y,          (x, 1), (x+1, -1))

        for i in range(self.gatesPerUnitCell):
            self.addWire( self.pl, None, None, self.gatesPerUnitCell*x+i,   (y,0), (y,1))

        # Source, Drain, Gate Connections

        grid_y0 = y*self.m2PerUnitCell + self.finDummy//2-1
        grid_y1 = grid_y0+(self.finsPerUnitCell - 2*self.finDummy + 2)//2
        gate_x = x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, None, gate_x , (grid_y0, -1), (grid_y1, 1))
        self.addVia( self.va, f'{fullname}:G', None, gate_x, (y*self.m2PerUnitCell//2, 1))
        self._xpins[name]['G'].append(gate_x)
        # Connect Source & Drain
        if reflect:
            _connect_diffusion(gate_x + 1, 'S') #S
            _connect_diffusion(gate_x - 1, 'D') #D
        else:
            _connect_diffusion(gate_x - 1, 'S') #S
            _connect_diffusion(gate_x + 1, 'D') #D

    def _addBodyContact(self, x, y, yloc=None, name='M1'):
        fullname = f'{name}_X{x}_Y{y}'
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = x*gu + gu // 2
        self._xpins[name]['B'].append(gate_x)
        self.addWire( self.activeb, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.pb, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.m1, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        self.addVia( self.va, f'{fullname}:B', None, gate_x, (y+1)*h + self.lFin//4)
        self.addVia( self.v1, 'B', None, gate_x, (y+1)*h + self.lFin//4)
