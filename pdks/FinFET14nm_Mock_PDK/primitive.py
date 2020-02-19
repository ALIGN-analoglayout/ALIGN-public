from align.primitive import default

# Override default MOSGenerator._addMOS & _addBodyContact 
# (to add fin & LISD layers)

class MOSGenerator(default.MOSGenerator):

    def _addMOS( self, x, y, x_cells, name='M1', reflect=False, **parameters):

        # Draw default layers
        super()._addMOS(x, y, x_cells, name, reflect, **parameters)

        # Draw Technology Specific Layers
        if self.shared_diff == 1:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin_diff, None, None,  self.finsPerUnitCell*y+i, 0, 2*(x_cells+self.gateDummy))
        else:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1) 

        gate_x = x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        self.addWire( self.LISD, None, None, gate_x - 1, (y, 1), (y+1, -1))
        self.addWire( self.LISD, None, None, gate_x + 1, (y, 1), (y+1, -1))

    def _addBodyContact(self, x, y, x_cells, yloc=None, name='M1'):
        super()._addBodyContact(x, y, x_cells, yloc, name)
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = x*gu + gu // 2
        self.addWire( self.LISDb, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        if self.shared_diff == 1:
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin_diff, None, None,  self.finsPerUnitCell*y+i, 0, 2*(x_cells+self.gateDummy))
        else:
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)

#
# Default Cap & Res generators are good enough
#

CapGenerator = default.CapGenerator
ResGenerator = default.ResGenerator
