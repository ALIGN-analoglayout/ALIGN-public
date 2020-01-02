import datetime
import sys
import pathlib
import logging
import collections
import math

logger = logging.getLogger(__name__)

class DefaultPrimitiveGenerator():

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

        self.addWire( self.m2, 'B', 'B', ((y_cells)* self.m2PerUnitCell//2, self.lFin//4), (0, 1), (x_cells*self.gatesPerUnitCell, -1))

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
        self.addWire( self.LISDb, None, None, gate_x, ((y+1)*h+3, -1), ((y+1)*h+self.lFin//2-3, 1)) 
        self.addVia( self.va, f'{fullname}:B', None, gate_x, ((y+1)*h//2, self.lFin//4))
        self.addVia( self.v1, 'B', None, gate_x, ((y+1)*h//2, self.lFin//4))        
        for i in range(self.finsPerUnitCell, self.finsPerUnitCell+self.lFin):
            self.addWire( self.fin, None, None,  self.finsPerUnitCell*y+i, x, x+1)

    def _addMOSArray( self, x_cells, y_cells, pattern, connections, minvias = 2, **parameters):
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

    def addCap( self, unit_cap):

        x_length = float((math.sqrt(unit_cap/2))*1000)
        y_length = float((math.sqrt(unit_cap/2))*1000)  

        c_m1_p = self.pdk['Cap']['m1Pitch']
        c_m1_w = self.pdk['Cap']['m1Width']
        c_m2_p = self.pdk['Cap']['m2Pitch']
        c_m2_w = self.pdk['Cap']['m2Width']
        m1_p = self.pdk['M1']['Pitch']
        m2_p = self.pdk['M2']['Pitch']

        print( f"Pitches {c_m1_p} {c_m2_p} {m1_p} {m2_p}")

        def compute( l, p, w):
            # this is nonsense but if l is a multiple of 2p say 2kp, then 2kp+p-w/(2p) is always k
            return int( 2*round(  (l+p-w)/(2.0*p) ))

        x_number = compute( x_length, c_m1_p, c_m1_w)
        y_number = compute( y_length, c_m2_p, c_m2_w)

        print( f"Number of wires {x_number} {y_number}")

        def roundup( x, p):
            return (x+p-1)//p

        last_y1_track = roundup( (y_number-1)*c_m2_p, m2_p)
        last_x1_track = roundup( (x_number-1)*c_m1_p, m1_p)

        grid_y0 = 0
        grid_y1 = grid_y0 + last_y1_track

        for i in range(x_number-1):
            grid_x = i
            net = 'PLUS' if i%2 == 1 else 'MINUS'
            self.addWire( self.m1n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.m3n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))

            grid_y = ((i+1)%2)*grid_y1

            self.addVia( self.v1_nx, net, None, grid_x, grid_y)
            self.addVia( self.v2_nx, net, None, grid_x, grid_y)

        pin = 'PLUS'
        # Don't port m1 per Yaguang instructions
        self.addWire( self.m1, 'PLUS', None, last_x1_track, (grid_y0, -1), (grid_y1, 1))
        # don't port m3 (or port one or the other)
        self.addWire( self.m3, 'PLUS', None, last_x1_track, (grid_y0, -1), (grid_y1, 1))

        grid_x0 = 0
        grid_x1 = grid_x0 + last_x1_track

        for i in range(y_number-1):
            grid_x = ((i+1)%2)*grid_x1
            net = 'PLUS' if i%2 == 0 else 'MINUS'
            self.addVia( self.v1_xn, net, None, grid_x, i)
            self.addVia( self.v2_xn, net, None, grid_x, i)
            pin = 'PLUS' if i == 0 else None
            self.addWire( self.m2n, net, pin, i, (grid_x0, -1), (grid_x1, 1))

        pin = 'MINUS'
        self.addWire( self.m2, 'MINUS', pin, last_y1_track, (grid_x0, -1), (grid_x1, 1))

        self.addRegion( self.boundary, 'Boundary', None,
                        0, 0,
                        last_x1_track,
                        last_y1_track)

        print( "Computed Boundary:", self.terminals[-1], self.terminals[-1]['rect'][2], self.terminals[-1]['rect'][2]%80)

def get_xcells_pattern( primitive, pattern, x_cells):
    if any(primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # Dual transistor (current mirror) primitives
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*x_cells + 2
    elif any(primitive.startswith(f'{x}_') for x in ["SCM", "CMC", "DP", "CCP", "LS"]):
        # Dual transistor primitives
        x_cells = 2*x_cells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells%4 != 0 else pattern ### CC is not possible; default is interdigitated
    return x_cells, pattern

def get_parameters(primitive, parameters, nfin):
    if parameters is None:
        parameters = {}
    if 'model' not in parameters:
        parameters['model'] = 'NMOS' if 'NMOS' in primitive else 'PMOS'
    parameters['nfin'] = nfin
    return parameters

# TODO: Pass cell_pin and pattern to this function to begin with
def generate_MOS_primitive(uc, block_name, primitive, height, nfin, x_cells, y_cells, pattern, parameters, pinswitch):

    x_cells, pattern = get_xcells_pattern(primitive, pattern, x_cells)
    parameters = get_parameters(primitive, parameters, nfin)

    def gen( pattern, routing):
        if 'NMOS' in primitive:
            uc.addNMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        else:
            uc.addPMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        return routing.keys()

    if primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G')]})

    elif primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'G'), ('M1', 'D')]})

    elif primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G')],
                                 'DB': [('M2', 'D')],
                                 'GB': [('M2', 'G')]})
    elif primitive in ["Dummy_NMOS", "Dummy_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'G')],
                                 'D': [('M1', 'D')]})
    elif primitive in ["Dcap_NMOS", "Dcap_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'D')],
                                'G': [('M1', 'G')]})
    elif primitive in ["Dcap1_NMOS", "Dcap1_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'D'), ('M1', 'G')]})
    elif primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'DA': [('M1', 'D')],
                                 'SB': [('M2', 'S')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})


    elif primitive in ["CMC_NMOS_S", "CMC_PMOS_S"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})

    elif primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'GA': [('M1', 'G')],
                                 'GB': [('M2', 'G')]})

    elif primitive in ["LS_NMOS", "LS_PMOS"]:
        cell_pin = gen(pattern, {'SA':  [('M1', 'S')],
                                 'SB': [('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CCP_NMOS_S", "CCP_PMOS_S"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')]})

    elif primitive in ["CCP_NMOS", "CCP_PMOS"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'SB': [('M2','S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')]}) 

    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")

    return uc, cell_pin

def generate_Cap(uc, block_name, unit_cap):
    uc.addCap(unit_cap)

    return uc, ['PLUS', 'MINUS']

# WARNING: Bad code. Changing these default values breaks functionality.
def generate_primitive(block_name, primitive, height=12, x_cells=1, y_cells=1, pattern=1, value=12, parameters=None, pinswitch=0, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd()):

    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"
    sys.path.insert(0, str(pdkdir))
    import gen_gds_json
    import gen_lef
    from primitive import PrimitiveGenerator
    sys.path.pop(0)

    # TODO: THIS SHOULD NOT BE NEEDED !!!
    fin = height
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gate = 2

    uc = PrimitiveGenerator( fin, finDummy, gate, gateDummy)

    if 'MOS' in primitive:
        uc, cell_pin = generate_MOS_primitive(uc, block_name, primitive, height, value, x_cells, y_cells, pattern, parameters, pinswitch)
    elif 'Cap' in primitive:
        uc, cell_pin = generate_Cap(uc, block_name, value)
        uc.setBboxFromBoundary()
    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")

    with open(outputdir / (block_name + '.json'), "wt") as fp:
        uc.writeJSON( fp)

    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, cell_pin)
    with open( outputdir / (block_name + ".json"), "rt") as fp0, \
         open( outputdir / (block_name + ".gds.json"), 'wt') as fp1:
        gen_gds_json.translate(block_name, '', pinswitch, fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0))

    return uc
