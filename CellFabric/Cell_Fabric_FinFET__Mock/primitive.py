from canvas import FinFET_Mock_PDK_Canvas
from collections import defaultdict

class PrimitiveGenerator(FinFET_Mock_PDK_Canvas):

    def _addMOS( self, x, y, name='M1', reflect=False):

        def _connect_diffusion(x, name, pin):
            self.addWire( self.m1, None, None, x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.LISD, None, None, x, (y, 1), (y+1, -1))
            for j in range(((self.finDummy+3)//2), self.v0.h_clg.n):
                self.addVia( self.v0, f'{name}:{pin}', None, x, (y, j))
            self._xpins[name][pin].append(x)

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
        self.addVia( self.va, f'{name}:G', None, gate_x, (y*self.m2PerUnitCell//2, 1))
        self._xpins[name]['G'].append(gate_x)
        # Connect Source & Drain
        if reflect:
            _connect_diffusion(gate_x + 1, name, 'S') #S
            _connect_diffusion(gate_x - 1, name, 'D') #D
        else:
            _connect_diffusion(gate_x - 1, name, 'S') #S
            _connect_diffusion(gate_x + 1, name, 'D') #D

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

    def _addMOSArray( self, x_cells, y_cells, pattern, Routing):
        names = ['M1'] if pattern == 0 else ['M1', 'M2']
        self._dbg = []
        for y in range(y_cells):
            self._xpins = defaultdict(lambda: defaultdict(list))
            self._dbg.append([])
            for x in range(x_cells):
                if pattern == 0: # None (single transistor)
                    # TODO: Not sure this works without dummies. Currently:
                    # A A A A A A
                    self._addMOS(x, y, names[0], False)
                    self._dbg[-1].append( (names[0], False) )
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    self._addMOS(x, y, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2)
                    self._dbg[-1].append( (names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2) )
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, names[((x % 2) + (y % 2)) % 2], False)
                    self._dbg[-1].append( (names[((x % 2) + (y % 2)) % 2], False) )
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False)
                    self._dbg[-1].append( (names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False) )
                else:
                    assert False, "Unknown pattern"
            self._addRouting(y, y_cells, Routing)

    def addNMOSArray( self, x_cells, y_cells, pattern, Routing):

        self._addMOSArray(x_cells, y_cells, pattern, Routing)

        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)

    def addPMOSArray( self, x_cells, y_cells, pattern, Routing):

        self._addMOSArray(x_cells, y_cells, pattern, Routing)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
