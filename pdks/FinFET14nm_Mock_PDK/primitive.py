from canvas import FinFET14nm_Mock_PDK_Canvas
from align.cell_fabric import DefaultPrimitiveGenerator

import logging
logger = logging.getLogger(__name__)

class PrimitiveGenerator(FinFET14nm_Mock_PDK_Canvas, DefaultPrimitiveGenerator):

    def _addMOS( self, x, y, name='M1', reflect=False, **parameters):

        # Draw default layers
        super()._addMOS(x, y, name, reflect, **parameters)

        # Draw Technology Specific Layers
        self.addWire( self.RVT,  None, None, y,          (x, 1), (x+1, -1))

        gate_x = x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        self.addWire( self.LISD, None, None, gate_x - 1, (y, 1), (y+1, -1))
        self.addWire( self.LISD, None, None, gate_x + 1, (y, 1), (y+1, -1))