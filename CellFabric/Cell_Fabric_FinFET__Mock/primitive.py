from canvas import FinFET_Mock_PDK_Canvas
from collections import defaultdict

import logging
logger = logging.getLogger(__name__)

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

    def _connectDevicePins(self, y, connections, pinned=False):
        center_track = y * self.m2PerUnitCell + self.m2PerUnitCell // 2 # Used for m1 extension
        for track, (net, conn) in enumerate(connections.items(), start=1):
            contacts = {track for inst, pins in self._xpins.items()
                              for pin, m1tracks in pins.items()
                              for track in m1tracks if (inst, pin) in conn}
            for j in range(self.minvias):
                current_track = y * self.m2PerUnitCell + len(connections) * j + track
                self.addWireAndViaSet(net, net if pinned else None, self.m2, self.v1, current_track, contacts)
                self._nets[net][current_track] = contacts
                # Extend m1 if needed. TODO: Should we draw longer M1s to begin with?
                direction = 1 if current_track > center_track else -1
                for i in contacts:
                    self.addWire( self.m1, None, None, i, (center_track, -1 * direction), (current_track, direction))

    def _connectNets(self, x_cells, y_cells):
        m3start = (x_cells * self.gatesPerUnitCell - len(self._nets) * self.minvias) // 2
        for track, (net, conn) in enumerate(self._nets.items(), start=1):
            for j in range(self.minvias):
                current_track = m3start + len(self._nets) * j + track
                contacts = conn.keys()
                self.addWireAndViaSet(net, net, self.m3, self.v2, current_track, contacts)
                # Extend m2 if needed. TODO: What to do if we go beyond cell boundary?
                for i, locs in conn.items():
                    self.addWire(self.m2, None, None, i, (min(*locs, current_track), -1), (max(*locs, current_track), 1))

    def _addMOSArray( self, x_cells, y_cells, pattern, connections, minvias = 2):
        if minvias * len(connections) > self.m2PerUnitCell - 1:
            self.minvias = (self.m2PerUnitCell - 1) // len(connections)
            logger.warning( f"Using minvias = {self.minvias}. Cannot route {len(connections)} signals using minvias = {minvias} (max m2 / unit cell = {self.m2PerUnitCell})" )
        else:
            self.minvias = minvias
        names = ['M1'] if pattern == 0 else ['M1', 'M2']
        self._nets = defaultdict(lambda: defaultdict(list)) # net:m2track:m1contacts (Updated by self._connectDevicePins)
        for y in range(y_cells):
            self._xpins = defaultdict(lambda: defaultdict(list)) # inst:pin:m1tracks (Updated by self._addMOS)
            for x in range(x_cells):
                if pattern == 0: # None (single transistor)
                    # TODO: Not sure this works without dummies. Currently:
                    # A A A A A A
                    self._addMOS(x, y, names[0], False)
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    self._addMOS(x, y, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2)
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, names[((x % 2) + (y % 2)) % 2], False)
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False)
                else:
                    assert False, "Unknown pattern"
            self._connectDevicePins(y, connections, y_cells == 1)
        if y_cells > 1:
            self._connectNets(x_cells, y_cells)

    def addNMOSArray( self, x_cells, y_cells, pattern, connections):

        self._addMOSArray(x_cells, y_cells, pattern, connections)

        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)

    def addPMOSArray( self, x_cells, y_cells, pattern, connections):

        self._addMOSArray(x_cells, y_cells, pattern, connections)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell)
