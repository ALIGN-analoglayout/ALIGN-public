from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class MOSGenerator(DefaultCanvas):

    def __init__(self, pdk, fin, finDummy, gate, gateDummy):
        super().__init__(pdk)
        assert   3*self.pdk['Fin']['Pitch'] < 2*self.pdk['M2']['Pitch']

        ######### Derived Parameters ############
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy
        self.finDummy = finDummy
        self.lFin = 16 ## need to be added in the PDK JSON
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        assert fin > 3, "number of fins in the transistor must be more than 2"
        assert finDummy % 2 == 0
        assert gateDummy > 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell* self.pdk['M2']['Pitch']
        unitCellLength = self.gatesPerUnitCell* self.pdk['Poly']['Pitch']
        activeWidth =  self.pdk['Fin']['Pitch']*fin
        activeOffset = activeWidth//2 + finDummy*self.pdk['Fin']['Pitch']-self.pdk['Fin']['Pitch']//2
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*self.pdk['Active']['active_enclosure']

        self.pl = self.addGen( Wire( 'pl', 'Poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= self.pdk['Poly']['Pitch'], width= self.pdk['Poly']['Width'], offset= self.pdk['Poly']['Offset']),
                                     spg=SingleGrid( offset= self.pdk['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        stoppoint = (gateDummy-1)* self.pdk['Poly']['Pitch'] +  self.pdk['Poly']['Offset']
        self.active = self.addGen( Wire( 'active', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Wire( 'RVT', 'Rvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = activeOffset-activeWidth//2
        self.LISD = self.addGen( Wire( 'LISD', 'Lisd', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M1']['Pitch'], width=self.pdk['Lisd']['LisdWidth'], offset=self.pdk['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = gateDummy*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Offset']-self.pdk['Pc']['PcExt']-self.pdk['Poly']['Width']//2
        self.pc = self.addGen( Wire( 'pc', 'Pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pc']['PcWidth'], offset=self.pdk['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'Pselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'Nwell',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        stoppoint = unitCellLength//2-self.pdk['Active']['activebWidth_H']//2
        offset_active_body = (self.lFin//2)*self.pdk['Fin']['Pitch']+self.unitCellHeight-self.pdk['Fin']['Pitch']//2
        self.activeb = self.addGen( Wire( 'activeb', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Active']['activebWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = unitCellLength//2-self.pdk['Pb']['pbWidth_H']//2
        self.pb = self.addGen( Wire( 'pb', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.LISDb = self.addGen( Wire( 'LISDb', 'Lisd', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   self.pdk['M1']['Pitch'], width= self.pdk['Lisd']['LisdWidth'], offset= self.pdk['M1']['Offset']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], offset=0, stoppoint= self.pdk['M2']['Width']//2+self.pdk['V1']['VencA_L'], check=True)))

        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg))

        self.v0.h_clg.addCenterLine( 0,                 self.pdk['V0']['WidthY'], False)
        v0pitch = activeWidth//(2*self.pdk['M2']['Pitch']) * self.pdk['Fin']['Pitch']
        for i in range(activeWidth // v0pitch + 1):
            self.v0.h_clg.addCenterLine(i*v0pitch,    self.pdk['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    self.pdk['V0']['WidthY'], False)

        info = self.pdk['V0']
        def single_centered_via(rect):
            xpos = ( rect[0] + rect[2] ) // 2
            ypos = ( rect[1] + rect[3] ) // 2
            return [xpos - info['WidthX'] // 2, ypos - info['WidthY'] // 2, xpos + info['WidthX'] // 2, ypos + info['WidthY'] // 2]

        self.postprocessor.register('V0', single_centered_via)

    def _addMOS( self, x, y, name='M1', reflect=False, **parameters):

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

        self.addWire( self.m2, 'B', 'B', (y_cells)* self.m2PerUnitCell + self.lFin//4, (0, 1), (x_cells*self.gatesPerUnitCell, -1))

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

    def _addMOSArray( self, x_cells, y_cells, pattern, connections, minvias = 1, **parameters):
        if minvias * len(connections) > self.m2PerUnitCell - 1:
            self.minvias = (self.m2PerUnitCell - 1) // len(connections)
            logger.warning( f"Using minvias = {self.minvias}. Cannot route {len(connections)} signals using minvias = {minvias} (max m2 / unit cell = {self.m2PerUnitCell})" )
        else:
            self.minvias = minvias
        names = ['M1'] if pattern == 0 else ['M1', 'M2']
        self._nets = collections.defaultdict(lambda: collections.defaultdict(list)) # net:m2track:m1contacts (Updated by self._connectDevicePins)
        for y in range(y_cells):
            self._xpins = collections.defaultdict(lambda: collections.defaultdict(list)) # inst:pin:m1tracks (Updated by self._addMOS)
            for x in range(x_cells):
                if pattern == 0: # None (single transistor)
                    # TODO: Not sure this works without dummies. Currently:
                    # A A A A A A
                    self._addMOS(x, y, names[0], False, **parameters)
                    self._addBodyContact(x, y, y_cells - 1, names[0])
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    self._addMOS(x, y, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2, **parameters)
                    self._addBodyContact(x, y, y_cells - 1, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2])
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, names[((x % 2) + (y % 2)) % 2], False, **parameters)
                    self._addBodyContact(x, y, y_cells - 1, names[((x % 2) + (y % 2)) % 2])
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False, **parameters)
                    self._addBodyContact(x, y, y_cells - 1, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1])
                else:
                    assert False, "Unknown pattern"
            self._connectDevicePins(y, connections)
        self._connectNets(x_cells, y_cells) 

    def addNMOSArray( self, x_cells, y_cells, pattern, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, connections, **parameters)

        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+self.lFin) 

    def addPMOSArray( self, x_cells, y_cells, pattern, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, connections, **parameters)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+self.lFin)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell, -1), y_cells* self.finsPerUnitCell+self.lFin)
