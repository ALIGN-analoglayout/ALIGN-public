from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric.generators import *
from align.cell_fabric.grid import *
from math import floor, ceil

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
        self.shared_diff = 1
        self.stack = stack
        self.bodyswitch = bodyswitch
        self.gateDummy = 2
        self.gate = 2*gate if self.stack ==1 else gate*self.stack
        self.gatesPerUnitCell = self.gate + 2*self.gateDummy*(1-self.shared_diff)
        self.finDummy = (self.finsPerUnitCell-fin)//2
        self.lFin = 8 ### This defines numebr of fins for tap cells; Should we define it in the layers.json?
        assert self.finDummy >= 8, "number of fins in the transistor must be less than height"
        assert fin > 1, "number of fins in the transistor must be more than 1" 
        assert gateDummy > 0
        unitCellLength = self.gatesPerUnitCell* self.pdk['Poly']['Pitch']
        activeOffset = self.unitCellHeight//2 - self.pdk['Fin']['Pitch']//2
        self.activeWidth =  self.pdk['Fin']['Pitch']*fin
        activePitch = self.unitCellHeight
        RVTWidth = self.activeWidth + 2*self.pdk['Active']['active_enclosure']


        stoppoint = self.pdk['Active']['activePolyExTracks']*self.pdk['M2']['Pitch']
        self.pl = self.addGen( Wire( 'pl', 'Poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= self.pdk['Poly']['Pitch'], width= self.pdk['Poly']['Width'], offset= self.pdk['Poly']['Offset']),
                                     spg=EnclosureGrid( pitch=self.unitCellHeight, offset=self.pdk['M2']['Offset'], stoppoint=stoppoint, check=True)))

        stoppoint = (self.unitCellHeight-self.activeWidth)//2 - self.pdk['Layer1']['Active_enclosure']
        self.layer1 = self.addGen( Wire( 'layer1', 'Layer1', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= self.gatesPerUnitCell*self.pdk['Poly']['Pitch'], width= self.pdk['Poly']['Pitch']+2*self.pdk['Layer1']['Offset'], offset= (self.gateDummy+1)*self.pdk['Poly']['Pitch']),
                                     spg=EnclosureGrid( pitch=self.unitCellHeight, offset=-self.pdk['Fin']['Pitch']//2, stoppoint=stoppoint, check=True)))

        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= self.pdk['Fin']['Pitch'], width= self.pdk['Fin']['Width'], offset= self.pdk['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        stoppoint = ((self.gateDummy-1)* self.pdk['Poly']['Pitch'] +  self.pdk['Poly']['Offset'])*(1-self.shared_diff)
        self.active = self.addGen( Wire( 'active', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Region( 'RVT', 'Rvt',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        self.LVT = self.addGen( Region( 'LVT', 'Lvt',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        self.HVT = self.addGen( Region( 'HVT', 'Hvt',
                                            v_grid=CenteredGrid( offset= self.pdk['Poly']['Pitch']//2, pitch= self.pdk['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
 
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
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=self.activeWidth, offset=activeOffset),
                                         spg=SingleGrid( pitch=self.pdk['Poly']['Pitch'], offset=(self.gateDummy-1)*self.pdk['Poly']['Pitch']+self.pdk['Poly']['Pitch']//2)))
        
        stoppoint = unitCellLength//2-self.pdk['Active']['activebWidth_H']//2
        self.activeb = self.addGen( Wire( 'activeb', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M2']['Pitch'], width=self.pdk['Active']['activebWidth'], offset= 0),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=self.gateDummy*self.pdk['Poly']['Pitch']*self.shared_diff-self.pdk['Poly']['Pitch'], stoppoint=stoppoint, check=True)))
          
        stoppoint = unitCellLength//2-self.pdk['Pb']['pbWidth_H']//2
        self.pb = self.addGen( Wire( 'pb', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=self.pdk['M2']['Pitch'], width=self.pdk['Pb']['pbWidth'], offset= 0),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=self.gateDummy*self.pdk['Poly']['Pitch']*self.shared_diff-self.pdk['Poly']['Pitch'], stoppoint=stoppoint, check=True)))

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
        v0pitch = self.pdk['V0']['WidthY'] + self.pdk['V0']['SpaceY']
        v0Offset = activeOffset - self.activeWidth//2 + self.pdk['V0']['VencA_L'] + self.pdk['V0']['WidthY']//2
        v0_number = floor((self.activeWidth-2*self.pdk['V0']['VencA_L']-self.pdk['V0']['WidthY'])/v0pitch + 1)
        assert v0_number > 0, "V0 can not be placed in the active region"
        v0_number = v0_number if v0_number < 4 else v0_number - 1 ## To avoid voilation of V0 enclosure by M1 DRC
        for i in range(v0_number):
            self.v0.h_clg.addCenterLine(i*v0pitch+v0Offset,    self.pdk['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    self.pdk['V0']['WidthY'], False)
        info = self.pdk['V0']

    def _addMOS( self, x, y, x_cells,  vt_type, name='M1', reflect=False, **parameters):
        fullname = f'{name}_X{x}_Y{y}'
        self.subinsts[fullname].parameters.update(parameters)

        def _connect_diffusion(i, pin):
            self.addWire( self.m1, None, i, (grid_y0-m1_length//2, -1), (grid_y0+m1_length//2, 1))
            for j in range(1,self.v0.h_clg.n): ## self.v0.h_clg.n??
                self.addVia( self.v0, f'{fullname}:{pin}', i, (y, j))
            self._xpins[name][pin].append(i)
            
        # Draw FEOL Layers
        if self.shared_diff == 0:
            self.addWire( self.active, None, y, (x,1), (x+1,-1)) 
        elif self.shared_diff == 1 and x == x_cells-1:
            self.addWire( self.active_diff, None, y, 0, self.gate*x_cells+1)
        else:
            pass
        self.addWire( self.layer1, None, x,   (y,1), (y+1,-1))
        if parameters['model'] == 'NMOS':
            if x == x_cells-1: self.addRegion( self.nselect, None, (1, -1), y* self.finsPerUnitCell+6, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), (y+1)* self.finsPerUnitCell-6) 
        else:
            if x == x_cells-1: self.addRegion( self.pselect, None, (1, -1), y* self.finsPerUnitCell+6, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), (y+1)* self.finsPerUnitCell-6)

        for i in range(self.gate):
            self.addWire( self.pl, None, i+self.gatesPerUnitCell*x+self.gateDummy,   (y,1), (y+1,-1))

        # Source, Drain, Gate Connections
        grid_y0 = y*self.m2PerUnitCell + self.m2PerUnitCell//2
        m1_length = ceil(self.activeWidth/self.pdk['M2']['Pitch'])
        print(m1_length)
        grid_y1 = (y+1)*self.m2PerUnitCell-5
        gate_x = self.gateDummy*self.shared_diff + x * self.gatesPerUnitCell + self.gatesPerUnitCell // 2
        # Connect Gate (gate_x)
        self.addWire( self.m1, None, gate_x , (grid_y1+2, -1), (grid_y1+4, 1))
        self.addWire( self.pc, None, grid_y1+1, (x,1), (x+1,-1))
        self.addVia( self.va, f'{fullname}:G', gate_x, grid_y1+2)
        self._xpins[name]['G'].append(gate_x)

        # Connect Source & Drain
        SD_x = self.gateDummy + x * self.gatesPerUnitCell
        #(center_terminal, side_terminal) = ('S', 'D') if self.gate%4 == 0 else ('D', 'S')
        #center_terminal = 'D' if self.stack > 1 else center_terminal # for stacked devices
        #_connect_diffusion(gate_x, center_terminal)
        count = 0
        for x_terminal in range(0, self.gate+1, self.stack):
            if reflect:
                terminal = 'D' if count%2 == 0 else 'S'
                _connect_diffusion(SD_x + x_terminal, terminal)
            else:
                terminal = 'S' if count%2 == 0 else 'D'
                _connect_diffusion(SD_x + x_terminal, terminal)
            count = count + 1

    def _connectDevicePins(self, y, y_cells, connections):
        center_track = y * self.m2PerUnitCell + self.m2PerUnitCell // 2 # Used for m1 extension
        grid_y1 = (y+1)*self.m2PerUnitCell-5
        gate_track = 0
        diff_track = self.m2PerUnitCell // 2 - ceil(self.activeWidth/self.pdk['M2']['Pitch'])-1
        print(diff_track)
        body_v0_track = (self.lFin*self.pdk['Fin']['Pitch'])//(2*self.pdk['M2']['Pitch'])
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
                        if y != y_cells-1 and y != 0: continue
                        if y==0:current_track = -1*body_v0_track
                        if y==y_cells-1:current_track = (y+1) * self.m2PerUnitCell + body_v0_track
                    else:
                        current_track = y * self.m2PerUnitCell + len(connections) * j + diff_track
                        diff_track = diff_track + 1
                    self.addWireAndViaSet(net, self.m2, self.v1, current_track, contacts)
                    self._nets[net][current_track] = contacts
                    if y_cells == 1 and pin == 'B':
                        current_track = -1*body_v0_track
                        self.addWireAndViaSet(net, self.m2, self.v1, current_track, contacts)
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
                    self.addWire(self.m2, net, i, (minx, -1), (maxx, 1), netType = 'pin')
                else: # create m3 terminal(s)
                    self.addWireAndViaSet(net, self.m3, self.v2, current_track, contacts, netType = 'pin')
                    if max(contacts) - min(contacts) < 2:
                        minL_m3 = 2 ## for M3 min length
                        maxy = min(contacts) + minL_m3
                        miny = min(contacts)
                        self.addWire(self.m3, net, current_track, (miny, -1), (maxy, 1), netType = 'pin')
                    else:
                        pass
                    # Extend m2 if needed. TODO: What to do if we go beyond cell boundary?
                    for i, locs in conn.items():
                        minx, maxx = _get_wire_terminators([*locs, current_track])
                        self.addWire(self.m2, net, i, (minx, -1), (maxx, 1))

    def _addBodyContact(self, x, y, x_cells, yloc=None, name='M1', **parameters):
        fullname = f'{name}_X{x}_Y{y}'

        if yloc is not None:
            y = yloc
        h = self.m2PerUnitCell
        gu = self.gatesPerUnitCell
        body_v0_track = (self.lFin*self.pdk['Fin']['Pitch'])//(2*self.pdk['M2']['Pitch'])
        gate_x = self.gateDummy*self.shared_diff + x*gu + gu // 2 - 1
        self._xpins[name]['B'].append(gate_x)
        ### FEOL layers
        self.addWire( self.activeb, None, (y+1)*h + body_v0_track, (x,1), (x+1,-1))
        self.addWire( self.activeb, None, -1*body_v0_track, (x,1), (x+1,-1))
        self.addWire( self.pb, None, (y+1)*h + body_v0_track, (x,1), (x+1,-1)) 
        ##Via and routing
        self.addWire( self.m1, None, gate_x, ((y+1)*h + body_v0_track-1, -1), ((y+1)*h + body_v0_track+1, 1))
        self.addVia( self.va, f'{fullname}:B', gate_x, (y+1)*h + body_v0_track)
        self.addWire( self.m1, None, gate_x, (-1*body_v0_track+1, 1), (-1*body_v0_track-1, -1))
        self.addVia( self.va, f'{fullname}:B', gate_x, -1*body_v0_track)

        if parameters['model'] == 'NMOS':
            self.addRegion( self.pselect, None, (1, -1), (y+1)* self.finsPerUnitCell+self.lFin//2-2, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), (y+1)* self.finsPerUnitCell+self.lFin//2+2)
            self.addRegion( self.pselect, None, (1, -1), -self.lFin//2-2, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), -self.lFin//2+2)
        else:
            self.addRegion( self.nselect, None, (1, -1), (y+1)*self.finsPerUnitCell+self.lFin//2-2, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), (y+1)* self.finsPerUnitCell+self.lFin//2+2)
            self.addRegion( self.nselect, None, (1, -1), -self.lFin//2-2, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), -self.lFin//2+2)

    def _addMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, minvias = 1, **parameters):

        def _addRVT(x_cells, y_cells):
            self.addRegion( self.RVT, None, (0, -1), -self.bodyswitch*self.lFin, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)

        def _addLVT(x_cells, y_cells):
            self.addRegion( self.LVT, None, (0, -1), -self.bodyswitch*self.lFin, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
    
        def _addHVT(x_cells, y_cells):
            self.addRegion( self.HVT, None, (0, -1), -self.bodyswitch*self.lFin, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)

        if vt_type == 'RVT':
            _addRVT(x_cells, y_cells)
        elif vt_type == 'LVT':
            _addLVT(x_cells, y_cells)
        elif vt_type == 'HVT':
            _addHVT(x_cells, y_cells)
        else:
            print("This VT type not supported")
            exit()

        if minvias * len(connections) > self.m2PerUnitCell - 1:
            self.minvias = (self.m2PerUnitCell - 1) // len(connections)
            logger.warning( f"Using minvias = {self.minvias}. Cannot route {len(connections)} signals using minvias = {minvias} (max m2 / unit cell = {self.m2PerUnitCell})" )
        else:
            self.minvias = minvias
        names = ['M1'] if pattern == 0 else ['M1', 'M2']
        self._nets = collections.defaultdict(lambda: collections.defaultdict(list)) # net:m2track:m1contacts (Updated by self._connectDevicePins)
        ### Needs to be generalized
        if len(parameters) > 2:
            device_name_all = [*parameters.keys()]
            if int(parameters[device_name_all[0]]["NFIN"])*int(parameters[device_name_all[0]]["NF"])*int(parameters[device_name_all[0]]["M"]) != int(parameters[device_name_all[1]]["NFIN"])*int(parameters[device_name_all[1]]["NF"])*int(parameters[device_name_all[1]]["M"]):
                pattern=3
                if int(parameters[device_name_all[0]]["NF"])*int(parameters[device_name_all[0]]["M"]) > int(parameters[device_name_all[1]]["NF"])*int(parameters[device_name_all[1]]["M"]):
                    x_left = x_cells//2 - (int(parameters[device_name_all[1]]["NF"])*int(parameters[device_name_all[1]]["M"]))//2
                    x_right = x_cells//2 + (int(parameters[device_name_all[1]]["NF"])*int(parameters[device_name_all[1]]["M"]))//2
                else:
                    x_left = x_cells//2 - (int(parameters[device_name_all[0]]["NF"])*int(parameters[device_name_all[0]]["M"]))//2
                    x_right = x_cells//2 + (int(parameters[device_name_all[0]]["NF"])*int(parameters[device_name_all[0]]["M"]))//2
         ##########################
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
                    self._addMOS(x, y, x_cells, vt_type, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], False,  **parameters)
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], **parameters)
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, x_cells, vt_type, names[((x % 2) + (y % 2)) % 2], False,  **parameters)   
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x % 2) + (y % 2)) % 2], **parameters)
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    self._addMOS(x, y, x_cells, vt_type, names[0 if x_left <= x < x_right else 1], False,  **parameters)
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[0 if x_left <= x < x_right else 1], **parameters)
                elif pattern == 5: # Rad-Hard interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, x_cells, vt_type, names[((x % 2) + (y % 2)) % 2], x%2,  **parameters)   
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x % 2) + (y % 2)) % 2], **parameters)
                elif pattern == 6: # Rad-Hard CC
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    self._addMOS(x, y, x_cells, vt_type, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x%2,  **parameters)   
                    if self.bodyswitch==1:self._addBodyContact(x, y, x_cells, y_cells - 1, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], **parameters)
                else:
                    assert False, "Unknown pattern"
            self._connectDevicePins(y, y_cells, connections)
        self._connectNets(x_cells, y_cells)
 
    def addNMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, connections, **parameters)
        #####   Nselect Placement   #####
        #self.addRegion( self.nselect, None, (2, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-2, -1), y_cells* self.finsPerUnitCell)
        #if self.bodyswitch==1:self.addRegion( self.pselect, None, (2, -1), y_cells* self.finsPerUnitCell, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-2, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)

    def addPMOSArray( self, x_cells, y_cells, pattern, vt_type, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, connections, **parameters)

        #####   Pselect and Nwell Placement   #####
        #self.addRegion( self.pselect, None, (2, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-2, -1), y_cells* self.finsPerUnitCell)
        #if self.bodyswitch==1:self.addRegion( self.nselect, None, (2, -1), y_cells* self.finsPerUnitCell, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-2, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
        self.addRegion( self.nwell, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff-1, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
