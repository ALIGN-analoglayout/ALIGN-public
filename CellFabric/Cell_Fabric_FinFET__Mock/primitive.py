from canvas import FinFET_Mock_PDK_Canvas

class PrimitiveGenerator(FinFET_Mock_PDK_Canvas):

    def _addMOS( self, x, y, reflect=False):

        def _connect_diffusion(x, port):
            self.addWire( self.m1, None, None, x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.LISD, None, None, x, (y, 1), (y+1, -1))
            for j in range(((self.finDummy+3)//2), self.v0.h_clg.n):
                self.addVia( self.v0, port, None, x, (y, j))

        # Draw FEOL Layers

        self.addWire( self.active, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.RVT,    None,    None, y, (x, 1), (x+1, -1))
        self.addWire( self.pc, None, None, y, (x,1), (x+1,-1))
        for i in range(1,  self.finsPerUnitCell):
            self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)
        for i in range(self.gatesPerUnitCell):
            self.addWire( self.pl, None, None, self.gatesPerUnitCell*x+i,   (y,0), (y,1))

        # Source, Drain, Gate Connections

        grid_y0 = y*self.m2PerUnitCell + self.finDummy//2-1
        grid_y1 = grid_y0+(self.finsPerUnitCell - 2*self.finDummy + 2)//2
        gate_x = x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, None, gate_x , (grid_y0, -1), (grid_y1, 1))
        self.addVia( self.va, None, None, gate_x, (y*self.m2PerUnitCell//2, 1))
        # Connect Source & Drain
        if reflect:
            _connect_diffusion(gate_x - 1, None) #D
            _connect_diffusion(gate_x + 1, None) #S
        else:
            _connect_diffusion(gate_x - 1, None) #S
            _connect_diffusion(gate_x + 1, None) #D

    def _addRouting(self, y, y_cells, Routing):
        for (pin, contact, track, m3route) in Routing(y):
            if y_cells > 1:
                self.addWire( self.m2, pin, None, y*self.m2PerUnitCell+track, (min(contact), -1), (max(contact), 1))
                self.addWire( self.m3, pin, pin, m3route, (track, -1), (y*self.m2PerUnitCell+track, 1))
                self.addVia( self.v2, None, None, m3route, track)
                self.addVia( self.v2, None, None, m3route, y*self.m2PerUnitCell+track)
            else:
                self.addWire( self.m2, pin, pin, y*self.m2PerUnitCell+track, (min(contact), -1), (max(contact), 1))

            for i in contact:
                self.addVia( self.v1, None, None, i, y*self.m2PerUnitCell+track)

    def _addMOSArray( self, x_cells, y_cells, Routing):
        for y in range(y_cells):
            for x in range(x_cells):
                self._addMOS(x, y)
            self._addRouting(y, y_cells, Routing)

    def addNMOSArray( self, x_cells, y_cells, Routing):

        self._addMOSArray(x_cells, y_cells, Routing)

        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)

    def addPMOSArray( self, x_cells, y_cells, Routing):

        self._addMOSArray(x_cells, y_cells, Routing)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
