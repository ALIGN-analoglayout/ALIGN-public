from canvas import FinFET14nm_Mock_PDK_Canvas
from collections import defaultdict

import logging
logger = logging.getLogger(__name__)

class PrimitiveGenerator(FinFET14nm_Mock_PDK_Canvas):

    def _addMOS( self, x, y, name='M1', reflect=False, **parameters):

        fullname = f'{name}_X{x}_Y{y}'
        self.subinsts[fullname].parameters.update(parameters)

        def _connect_diffusion(i, pin):
            self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.LISD, None, None, i, (y, 1), (y+1, -1))
            for j in range(((self.finDummy+3)//2), self.v0.h_clg.n):
                self.addVia( self.v0, f'{fullname}:{pin}', None, i, (y, j))
            self._xpins[name][pin].append(i)

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
        self.addVia( self.va, f'{fullname}:G', None, gate_x, (y*self.m2PerUnitCell//2, 1))
        self._xpins[name]['G'].append(gate_x)
        # Connect Source & Drain
        if reflect:
            _connect_diffusion(gate_x + 1, 'S') #S
            _connect_diffusion(gate_x - 1, 'D') #D
        else:
            _connect_diffusion(gate_x - 1, 'S') #S
            _connect_diffusion(gate_x + 1, 'D') #D

    def _connectDevicePins(self, y, connections):
        center_track = y * self.m2PerUnitCell + self.m2PerUnitCell // 2 # Used for m1 extension
        for track, (net, conn) in enumerate(connections.items(), start=1):
            contacts = {track for inst, pins in self._xpins.items()
                              for pin, m1tracks in pins.items()
                              for track in m1tracks if (inst, pin) in conn}
            for j in range(self.minvias):
                current_track = y * self.m2PerUnitCell + len(connections) * j + track
                self.addWireAndViaSet(net, None, self.m2, self.v1, current_track, contacts)
                self._nets[net][current_track] = contacts
                # Extend m1 if needed. TODO: Should we draw longer M1s to begin with?
                direction = 1 if current_track > center_track else -1
                for i in contacts:
                    self.addWire( self.m1, net, None, i, (center_track, -1 * direction), (current_track, direction))


    def _connectNets(self, x_cells, y_cells): 
        
        def _get_wire_terminators(intersecting_tracks):
            minx, maxx = min(intersecting_tracks), max(intersecting_tracks)
            # BEGIN: Quick & dirty MinL DRC error fix.
            minL = 2 # TODO: Make this MinL dependent
            L = maxx - minx
            if center_track - minL // 2 <= minx and maxx <= center_track + minL // 2:
                minx, maxx = (center_track - minL // 2, center_track + minL // 2)
            elif L < minL:
                minx, maxx = (minx - (minL - L), maxx) if minx >= center_track else (minx, maxx + (minL - L))
            # END: Quick & dirty MinL DRC error fix.
            return (minx, maxx)

        center_track = (x_cells * self.gatesPerUnitCell) // 2
        m3start = (x_cells * self.gatesPerUnitCell - len(self._nets) * self.minvias) // 2
        for track, (net, conn) in enumerate(self._nets.items(), start=1):
            for j in range(self.minvias):
                current_track = m3start + len(self._nets) * j + track
                contacts = conn.keys()
                if len(contacts) == 1: # Create m2 terminal
                    i = next(iter(contacts))
                    minx, maxx = _get_wire_terminators(conn[i])
                    self.addWire(self.m2, net, net, i, (minx, -1), (maxx, 1))
                else: # create m3 terminal(s)
                    self.addWireAndViaSet(net, net, self.m3, self.v2, current_track, contacts)
                    # Extend m2 if needed. TODO: What to do if we go beyond cell boundary?
                    for i, locs in conn.items():
                        minx, maxx = _get_wire_terminators([*locs, current_track])
                        self.addWire(self.m2, net, None, i, (minx, -1), (maxx, 1))

    def _bodyContact(self, x, y, x_cells, name='M1'):
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = x*gu + gu // 2
        self._xpins[name]['B'].append(gate_x)
        fullname = f'{name}_X{x}_Y{y}'
        self.addWire( self.activeb, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.pb, None, None, y, (x,1), (x+1,-1)) 
        self.addWire( self.m1, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        self.addWire( self.LISDb, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1)) 
        self.addVia( self.va, f'{fullname}:B', None, gate_x, ((y+1)*h//2, self.lFin//4))
        self.addVia( self.v1, f'{fullname}', None, gate_x, ((y+1)*h//2, self.lFin//4))
        
        for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
            self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)
        if x == x_cells-1:
            self.addWire( self.m2, 'B', 'B', ((y+1)*h//2, self.lFin//4), (0, 1), (x_cells*gu, -1))
    def _addMOSArray( self, x_cells, y_cells, pattern, connections, minvias = 2, **parameters):
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
                    self._addMOS(x, y, names[0], False, **parameters)
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    self._addMOS(x, y, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2, **parameters)
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, names[((x % 2) + (y % 2)) % 2], False, **parameters)
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False, **parameters)
                else:
                    assert False, "Unknown pattern"
                if y == y_cells-1:
                    for x in range(x_cells):
                        self._bodyContact(x, y, x_cells, names[0 if pattern == 0 else x_cells%2])
            self._connectDevicePins(y, connections)
        self._connectNets(x_cells, y_cells)

    def addNMOSArray( self, x_cells, y_cells, pattern, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, connections, **parameters)

        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+self.lFin) 

    def addPMOSArray( self, x_cells, y_cells, pattern, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, connections, **parameters)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+slef.lFin)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+self.lFin)
