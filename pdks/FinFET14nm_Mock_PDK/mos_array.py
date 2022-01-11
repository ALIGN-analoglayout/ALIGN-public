from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric.generators import *
from align.cell_fabric.grid import *
from . import MOSGenerator

import logging
logger = logging.getLogger(__name__)

class MOSArrayGenerator(DefaultCanvas):

    def __init__(self, pdk, height, bodyswitch):
        super().__init__(pdk)
        self.pdk = pdk
        self.finsPerUnitCell = height
        assert self.finsPerUnitCell % 4 == 0
        assert (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])%self.pdk['M2']['Pitch']==0
        self.m2PerUnitCell = (self.finsPerUnitCell*self.pdk['Fin']['Pitch'])//self.pdk['M2']['Pitch']
        self.unitCellHeight = self.m2PerUnitCell* self.pdk['M2']['Pitch']


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
                    self.addWireAndViaSet(net, self.m2, self.v1, current_track, contacts)
                    self._nets[net][current_track] = contacts
                # Extend m1 if needed. TODO: Should we draw longer M1s to begin with?
                #direction = 1 if current_track > center_track else -1
                #for i in contacts:
                #    self.addWire( self.m1, net, None, i, (center_track, -1 * direction), (current_track, direction))


    def _connectNets(self, x_cells, y_cells, gatesPerUnitCell):
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

        center_track = (x_cells * gatesPerUnitCell) // 2
        m3start = self.shared_diff+(x_cells * gatesPerUnitCell - len(self._nets) * self.minvias) // 2
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

    def _addMOSArray( self, x_cells, y_cells, pattern, vt_type, fin, gate, gateDummy, shared_diff, stack, connections, minvias = 1, **parameters):
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
        MG = MOSGenerator(self.pdk, self.finsPerUnitCell, fin, gate, gateDummy, shared_diff, stack)
        for y in range(y_cells):
            self._xpins = collections.defaultdict(lambda: collections.defaultdict(list)) # inst:pin:m1tracks (Updated by self._addMOS)
            
            for x in range(x_cells):
                if pattern == 0: # None (single transistor)
                    # TODO: Not sure this works without dummies. Currently:
                    # A A A A A A
                    MG._addMOS(x, y, x_cells, vt_type, names[0], False, **parameters)
                    if self.bodyswitch==1:MG._addBodyContact(x, y, x_cells, y_cells - 1, names[0])
                elif pattern == 1: # CC
                    # TODO: Think this can be improved. Currently:
                    # A B B A A' B' B' A'
                    # B A A B B' A' A' B'
                    # A B B A A' B' B' A'
                    MG._addMOS(x, y, x_cells, vt_type, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2], x >= x_cells // 2,  **parameters)
                    if self.bodyswitch==1:MG._addBodyContact(x, y, x_cells, y_cells - 1, names[((x // 2) % 2 + x % 2 + (y % 2)) % 2])
                elif pattern == 2: # interdigitated
                    # TODO: Evaluate if this is truly interdigitated. Currently:
                    # A B A B A B
                    # B A B A B A
                    # A B A B A B
                    MG._addMOS(x, y, x_cells, vt_type, names[((x % 2) + (y % 2)) % 2], False,  **parameters)   
                    if self.bodyswitch==1:MG._addBodyContact(x, y, x_cells, y_cells - 1, names[((x % 2) + (y % 2)) % 2])
                elif pattern == 3: # CurrentMirror
                    # TODO: Evaluate if this needs to change. Currently:
                    # B B B A A B B B
                    # B B B A A B B B
                    MG._addMOS(x, y, x_cells, vt_type, names[0 if x_left <= x < x_right else 1], False,  **parameters)
                    if self.bodyswitch==1:MG._addBodyContact(x, y, x_cells, y_cells - 1, names[0 if x_left <= x < x_right else 1])
                else:
                    assert False, "Unknown pattern"
            self._connectDevicePins(y, y_cells, connections)
        self._connectNets(x_cells, y_cells)

    def addNMOSArray( self, x_cells, y_cells, pattern, vt_type, fin, gate, gateDummy, shared_diff, stack, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, fin, gate, gateDummy, shared_diff, stack, connections, **parameters)
        #####   Nselect Placement   #####
        #self.addRegion( self.nselect, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin) 

    def addPMOSArray( self, x_cells, y_cells, pattern, vt_type, fin, gate, gateDummy, shared_diff, stack, connections, **parameters):

        self._addMOSArray(x_cells, y_cells, pattern, vt_type, fin, gate, gateDummy, shared_diff, stack, connections, **parameters)

        #####   Pselect and Nwell Placement   #####
        #self.addRegion( self.pselect, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)
        #self.addRegion( self.nwell, None, (0, -1), 0, (x_cells*self.gatesPerUnitCell+2*self.gateDummy*self.shared_diff, -1), y_cells* self.finsPerUnitCell+self.bodyswitch*self.lFin)

