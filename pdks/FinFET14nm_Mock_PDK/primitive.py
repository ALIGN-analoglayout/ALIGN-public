from align.primitive import default

# Override default MOSGenerator._addMOS & _addBodyContact 
# (to add fin & LISD layers)

class MOSGenerator(default.MOSGenerator):

    def _addMOS( self, x, y, x_cells, vt_type, name='M1', reflect=False, **parameters):

        # Draw default layers
        super()._addMOS(x, y, x_cells, vt_type, name, reflect, **parameters)

        # Draw Technology Specific Layers
        if self.shared_diff == 1:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin_diff, None, self.finsPerUnitCell*y+i, 0, (self.gate*x_cells+2*self.gateDummy))
        else:
            for i in range(1,  self.finsPerUnitCell):
                self.addWire( self.fin, None, self.finsPerUnitCell*y+i, x, x+1) 

        gate_x = self.gateDummy*self.shared_diff + x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2         
        self.addWire( self.LISD, None, gate_x - 1, (y, 1), (y+1, -1))
        self.addWire( self.LISD, None, gate_x + 1, (y, 1), (y+1, -1)) 
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


    def _addBodyContact(self, x, y, x_cells, yloc=None, name='M1'):
        super()._addBodyContact(x, y, x_cells, yloc, name)
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = self.gateDummy*self.shared_diff + x*gu + gu // 2
        self.addWire( self.LISDb, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        if self.shared_diff == 1:
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin_diff, None, self.finsPerUnitCell*y+i, 0, (self.gate*x_cells+2*self.gateDummy))
        else:
            for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
                self.addWire( self.fin, None, self.finsPerUnitCell*y+i, x, x+1)

#
# Default Cap & Res generators are good enough
#

CapGenerator = default.CapGenerator
ResGenerator = default.ResGenerator
RingGenerator = default.RingGenerator
# Default Via Array generator is good enough
ViaArrayGenerator = default.ViaArrayGenerator
