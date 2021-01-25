from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class MOSGenerator(DefaultCanvas):

    def __init__(self, pdk, height, fin, gate, gateDummy, shared_diff, stack, bodyswitch):
        super().__init__(pdk)
        self.finsPerUnitCell = height
        assert self.finsPerUnitCell % 4 == 0
        assert (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])%self.pdk['M2']['Pitch']==0
        self.m2PerUnitCell = (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])//self.pdk['M2']['Pitch']
        self.unitCellHeight = self.m2PerUnitCell* self.pdk['M2']['Pitch']
        ######### Derived Parameters ############
        self.shared_diff = shared_diff
        self.stack = stack
        self.bodyswitch = bodyswitch
        self.gateDummy = gateDummy
        self.gate = (2*gate)*self.stack
        self.gatesPerUnitCell = self.gate + 2*self.gateDummy*(1-self.shared_diff)
        self.finDummy = (self.finsPerUnitCell-fin)//2
        self.lFin = 16 ## need to be added in the PDK JSON
        assert self.finDummy >= 8, "number of fins in the transistor must be less than height"
        assert fin > 3, "number of fins in the transistor must be more than 2"
        assert fin % 2 == 0, "number of fins in the transistor must be even" 
        assert gateDummy > 0
        unitCellLength = self.gatesPerUnitCell* self.pdk['Poly']['Pitch']
        #activeOffset = self.finsPerUnitCell//-self.pdk['Fin']['Pitch']//2
        activeOffset = self.unitCellHeight//2 -self.pdk['Fin']['Pitch']//2
        activeWidth =  self.pdk['Fin']['Pitch']*fin
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*self.pdk['Active']['active_enclosure']

        self.pl = self.addGen( Wire( 'pl', 'Poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= self.pdk['Poly']['Pitch'], width= self.pdk['Poly']['Width'], offset= self.pdk['Poly']['Offset']),
                                     spg=SingleGrid( offset= self.pdk['M2']['Offset'], pitch=self.unitCellHeight)))


        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        self.fin_diff = self.addGen( Wire( 'fin_diff', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=self.pdk['Poly']['Pitch']))) 

        stoppoint = ((self.gateDummy-1)* self.pdk['Poly']['Pitch'] +  self.pdk['Poly']['Offset'])*(1-self.shared_diff)
        self.active = self.addGen( Wire( 'active', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Wire( 'RVT', 'Rvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
        
        self.LVT = self.addGen( Wire( 'LVT', 'Lvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.HVT = self.addGen( Wire( 'HVT', 'Hvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.SLVT = self.addGen( Wire( 'SLVT', 'Slvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = activeOffset-activeWidth//2
        self.LISD = self.addGen( Wire( 'LISD', 'Lisd', 'v',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M1']['Pitch'], width=self.pdk['Lisd']['LisdWidth'], offset=self.pdk['M1']['Offset']),
                                         spg=EnclosureGrid( pitch=self.unitCellHeight, offset=0, stoppoint=stoppoint, check=True)))

        offset = self.gateDummy*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Offset'] - self.pdk['Poly']['Pitch']//2
        stoppoint = self.gateDummy*self.pdk['Poly']['Pitch'] + self.pdk['Poly']['Offset']-self.pdk['Pc']['PcExt']-self.pdk['Poly']['Width']//2
        self.pc = self.addGen( Wire( 'pc', 'Pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M2']['Pitch'], width=self.pdk['Pc']['PcWidth'], offset=self.pdk['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=offset*self.shared_diff, stoppoint=stoppoint-offset*self.shared_diff, check=True)))

        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'Pselect',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'Nwell',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        self.active_diff = self.addGen( Wire( 'active_diff', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
        
        self.RVT_diff = self.addGen( Wire( 'RVT_diff', 'Rvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2))) 

        self.LVT_diff = self.addGen( Wire( 'LVT_diff', 'Lvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
   
        self.HVT_diff = self.addGen( Wire( 'HVT_diff', 'Hvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
        
        self.SLVT_diff = self.addGen( Wire( 'SLVT_diff', 'Slvt', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))

        stoppoint = unitCellLength//2-self.pdk['Active']['activebWidth_H']//2
        offset_active_body = (self.lFin//2)*self.pdk['Fin']['Pitch']+self.unitCellHeight-self.pdk['Fin']['Pitch']//2
        self.activeb = self.addGen( Wire( 'activeb', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Active']['activebWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
         
        self.activeb_diff = self.addGen( Wire( 'activeb_diff', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Active']['activebWidth'], offset=offset_active_body),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))

        self.pb_diff = self.addGen( Wire( 'pb_diff', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2))) 

        stoppoint = unitCellLength//2-self.pdk['Pb']['pbWidth_H']//2
        self.pb = self.addGen( Wire( 'pb', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.pdk['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.LISDb = self.addGen( Wire( 'LISDb', 'Lisd', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   self.pdk['M1']['Pitch'], width= self.pdk['Lisd']['LisdWidth'], offset= self.pdk['M1']['Offset']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], offset=0, stoppoint= self.pdk['M2']['Width']//2+self.pdk['V1']['VencA_L'], check=True)))

        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY']))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg,
                                    WidthX=self.pdk['V0']['WidthX'],
                                    WidthY=self.pdk['V0']['WidthY']))

        self.v0.h_clg.addCenterLine( 0,                 self.pdk['V0']['WidthY'], False)
        #v0pitch = activeWidth//(2*self.pdk['M2']['Pitch']) * self.pdk['Fin']['Pitch']
        v0pitch = 3*self.pdk['Fin']['Pitch']
        v0Offset = ((self.finDummy+3)//2)*self.pdk['M2']['Pitch'] 
        for i in range((activeWidth-2*self.pdk['M2']['Pitch']) // v0pitch + 1):
            self.v0.h_clg.addCenterLine(i*v0pitch+v0Offset,    self.pdk['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    self.pdk['V0']['WidthY'], False)
        info = self.pdk['V0']

    def _addMOS( self, x, y, x_cells,  vt_type, name='M1', reflect=False, **parameters):

        fullname = f'{name}_X{x}_Y{y}'
        self.subinsts[fullname].parameters.update(parameters)

        def _connect_diffusion(i, pin):
            self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
            for j in range(1,self.v0.h_clg.n): ## self.v0.h_clg.n??
                self.addVia( self.v0, f'{fullname}:{pin}', None, i, (y, j))
            self._xpins[name][pin].append(i)
            
        # Draw FEOL Layers
        if self.shared_diff == 0:
            self.addWire( self.active, None, None, y, (x,1), (x+1,-1)) 
        elif self.shared_diff == 1 and x == x_cells-1:
            self.addWire( self.active_diff, None, None, y, 0, self.gate*x_cells+1)
        else:
            pass

        for i in range(self.gatesPerUnitCell):
            self.addWire( self.pl, None, None, self.gatesPerUnitCell*x+self.gateDummy*self.shared_diff+i,   (y,0), (y,1))

        if self.shared_diff == 1 and (x == 0 or x == x_cells-1):
            dummy_gates = self.gatesPerUnitCell*x_cells+self.gateDummy if x == x_cells-1 else 0
            for i in range(self.gateDummy):
                self.addWire( self.pl, None, None, dummy_gates+i,   (y,0), (y,1))
        # Source, Drain, Gate Connections

        #grid_y0 = y*self.m2PerUnitCell + self.finDummy//2-1
        grid_y0 = y*self.m2PerUnitCell + 1
        grid_y1 = (y+1)*self.m2PerUnitCell-5
        #grid_y1 = grid_y0+(self.finsPerUnitCell - 2*self.finDummy + 2)//2-1
        gate_x = self.gateDummy*self.shared_diff + x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, None, gate_x , (grid_y1+2, -1), (grid_y1+4, 1))
        self.addWire( self.pc, None, None, grid_y1+1, (x,1), (x+1,-1))
        #self.addVia( self.va, f'{fullname}:G', None, gate_x, (y*self.m2PerUnitCell//2, 1))
        self.addVia( self.va, f'{fullname}:G', None, gate_x, grid_y1+2)
        self._xpins[name]['G'].append(gate_x)

        # Connect Source & Drain
        (center_terminal, side_terminal) = ('S', 'D') if self.gate%4 == 0 else ('D', 'S')
        center_terminal = 'D' if self.stack > 1 else center_terminal # for stacked devices
        _connect_diffusion(gate_x, center_terminal)

        for x_terminal in range(1,1+self.gate//2):
            terminal = center_terminal if x_terminal%2 == 0 else side_terminal #for fingers
            if self.stack > 1 and x_terminal != self.gate//2: continue
            terminal = 'S' if self.stack > 1 else terminal 
            if reflect:
                _connect_diffusion(gate_x - x_terminal, terminal)
                _connect_diffusion(gate_x + x_terminal, terminal)
            else:
                _connect_diffusion(gate_x - x_terminal, terminal)
                _connect_diffusion(gate_x + x_terminal, terminal)

    def _connectDevicePins(self, y, y_cells, connections):
        center_track = y * self.m2PerUnitCell + self.m2PerUnitCell // 2 # Used for m1 extension
        grid_y1 = (y+1)*self.m2PerUnitCell-5
        gate_track = 0
        diff_track = 1
        for (net, conn) in connections.items():
            contactsx = {(track, pin) for inst, pins in self._xpins.items()
                              for pin, m1tracks in pins.items()
                              for track in m1tracks if (inst, pin) in conn}
            pins = {x[1] for x in contactsx}
            for pin in pins:
                contacts = {x[0] for x in contactsx if x[1]==pin}
                          
                for j in range(self.minvias):
                    if pin == 'G':
                        current_track = grid_y1 + 2 + gate_track
                        gate_track = gate_track+1
                    elif pin == 'B':
                        if y != y_cells-1:continue
                        current_track = y_cells * self.m2PerUnitCell + self.lFin//4
                    else:
                        current_track = y * self.m2PerUnitCell + len(connections) * j + diff_track
                        diff_track = diff_track + 1
                    self.addWireAndViaSet(net, None, self.m2, self.v1, current_track, contacts)
                    self._nets[net][current_track] = contacts
                # Extend m1 if needed. TODO: Should we draw longer M1s to begin with?
                #direction = 1 if current_track > center_track else -1
                #for i in contacts:
                #    self.addWire( self.m1, net, None, i, (center_track, -1 * direction), (current_track, direction))


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
        m3start = self.shared_diff+(x_cells * self.gatesPerUnitCell - len(self._nets) * self.minvias) // 2
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
                    if max(contacts) - min(contacts) < 2:
                        minL_m3 = 2 ## for M3 min length
                        maxy = min(contacts) + minL_m3
                        miny = min(contacts)
                        self.addWire(self.m3, net, net, current_track, (miny, -1), (maxy, 1))
                    else:
                        pass
                    # Extend m2 if needed. TODO: What to do if we go beyond cell boundary?
                    for i, locs in conn.items():
                        minx, maxx = _get_wire_terminators([*locs, current_track])
                        self.addWire(self.m2, net, None, i, (minx, -1), (maxx, 1))

        #self.addWire( self.m2, 'B', 'B', (y_cells)* self.m2PerUnitCell + self.lFin//4, (0, 1), (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1))

    def _addBodyContact(self, x, y, x_cells, yloc=None, name='M1'):
        #if self.bodyswitch == 0:continue
        fullname = f'{name}_X{x}_Y{y}'
        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        gate_x = self.gateDummy*self.shared_diff + x*gu + gu // 2
        #gate_x = x*gu + gu // 2
        self._xpins[name]['B'].append(gate_x)
        if self.shared_diff == 0:
            self.addWire( self.activeb, None, None, y, (x,1), (x+1,-1)) 
            self.addWire( self.pb, None, None, y, (x,1), (x+1,-1)) 
        else:
            self.addWire( self.activeb_diff, None, None, y, 0, self.gate*x_cells+1)
            self.addWire( self.pb_diff, None, None, y, (x,1), (x+1,-1))
        self.addWire( self.m1, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1))
        self.addVia( self.va, f'{fullname}:B', None, gate_x, (y+1)*h + self.lFin//4)
        #self.addVia( self.v1, 'B', None, gate_x, (y+1)*h + self.lFin//4)

    def _addMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, minvias = 1, **parameters):
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
                    self._addMOS(x, y, x_cells, vt_type, names[0], False, **parameters)
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[0])
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    self._addMOS(x, y, x_cells, vt_type, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2,  **parameters)
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2])
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, x_cells, vt_type, names[((x % 2) + (y % 2)) % 2], False,  **parameters)   
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x % 2) + (y % 2)) % 2])
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, x_cells, vt_type, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1], False,  **parameters)
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[0 if 0 <= ((x_cells // 2) - x) <= 1 else 1])
                else:
                    assert False, "Unknown pattern"
            self._connectDevicePins(y, y_cells, connections)
        self._connectNets(x_cells, y_cells) 

    def addNMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, connections, **parameters)
        #####   Nselect Placement   #####
        self.addRegion( self.nselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin) 

    def addPMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, connections, **parameters)

        #####   Pselect and Nwell Placement   #####
        self.addRegion( self.pselect, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
        self.addRegion( self.nwell, None, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
