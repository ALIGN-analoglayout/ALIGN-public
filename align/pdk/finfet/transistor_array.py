import math
from itertools import cycle, islice
from align.cell_fabric import transformation
from align.schema.transistor import Transistor, TransistorArray
from . import CanvasPDK, MOS

import logging
logger = logging.getLogger(__name__)
logger_func = logger.debug


class MOSGenerator(CanvasPDK):


    def __init__(self, *args, **kwargs):
        super().__init__()
        self.instantiated_cells = []


    def addNMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(x_cells, y_cells, pattern, vt_type, ports, **parameters)


    def addPMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(x_cells, y_cells, pattern, vt_type, ports, **parameters)


    def mos_array_temporary_wrapper(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):

        logger_func(f'x_cells={x_cells}, y_cells={y_cells}, pattern={pattern}, ports={ports}, parameters={parameters}')

        #################################################################################################
        # TODO: All of below goes away when TransistorArray is passed to mos_array as shown below
        for key in ['m', 'real_inst_type']:
            assert key in parameters, f'Missing transistor parameter {key}'
        assert 'nf' or 'stack' in parameters, f'Missing transistor parameter nf or stack'

        if 'nf' in parameters:
            nf = 'nf'
            device_type = 'parallel'
        elif 'stack' in parameters:
            nf = 'stack'
            device_type = 'stack'
        else:
            nf = device_type = None
            assert False, f'Either nf or stack parameter should be defined {parameters}'

        if 'w' in parameters:
            nfin = parameters['w'] * 1e10 // self.pdk['Fin']['Pitch']
            # w in the netlist is the effective total width for a single transistor 
            nfin = nfin // parameters[nf]
        elif 'nfin' in parameters:
            nfin = parameters['nfin']
        else:
            assert False, f'Either nfin or w parameter should be defined {parameters}'

        unit_transistor = Transistor(device_type=device_type,
                                     nf=parameters[nf],
                                     nfin=nfin,
                                     model_name=parameters['real_inst_type'])

        def find_ports(p, i):
            d = {}
            for (k, v) in p.items():
                for t in v:
                    if t[0] == i:
                        d[t[1]] = k
            return d

        p1 = find_ports(ports, 'M1')
        p = {1: p1}
        m = {1: parameters['m']}

        p2 = find_ports(ports, 'M2')
        if len(p2) > 1:
            m[2] = parameters['m']
            p[2] = p2

        self.transistor_array = TransistorArray(
            unit_transistor=unit_transistor,
            m=m,
            ports=p,
            n_rows=y_cells
        )
        # TODO: All of above goes away when TransistorArray is passed to mos_array as shown below
        #################################################################################################
        m = 2*parameters['m'] if pattern > 0 else parameters['m']
        self.n_row, self.n_col = self.validate_array(m, y_cells, x_cells)
        logger_func(f'x_cells={self.n_col}, y_cells={self.n_row} after legalization')

        if self.n_row * self.n_col != m:
            assert False, f'x_cells {self.n_row} by y_cells {self.n_col} not equal to m {m}'

        self.ports = ports
        self.mos_array()


    def mos_array(self):

        assert len(self.transistor_array.m) <= 2, f'Arrays of more than 2 devices not supported yet'

        if len(self.transistor_array.m) == 1:
            is_dual = False
        else:
            is_dual = True

        if 'B' in self.transistor_array.ports[1]:
            tap_map = {'B': self.transistor_array.ports[1]['B']}
        else:
            tap_map = {'B': 'B'}

        # Assign M2 tracks to prevent adjacent V2 violation
        track_pattern_1 = {'G':[6], 'S':[4], 'D':[2]}
        mg = MOS()
        tx_a_1 = mg.mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_1)

        if is_dual:
            track_pattern_2 = {}

            if   self.transistor_array.ports[2]['G'] == self.transistor_array.ports[1]['G']:
                track_pattern_2['G'] = [6]
            elif self.transistor_array.ports[2]['G'] == self.transistor_array.ports[1]['S']:
                track_pattern_2['G'] = [4]
            else:
                track_pattern_2['G'] = [5]

            if   self.transistor_array.ports[2]['S'] == self.transistor_array.ports[1]['S']:
                track_pattern_2['S'] = [4]
            elif self.transistor_array.ports[2]['S'] == self.transistor_array.ports[1]['D']:
                track_pattern_2['S'] = [2]
            else:
                track_pattern_2['S'] = [3]

            if   self.transistor_array.ports[2]['D'] == self.transistor_array.ports[1]['D']:
                track_pattern_2['D'] = [2]
            else:
                track_pattern_2['D'] = [1]

            # Alternate m2 tracks for device A and device B for improved matching
            mg = MOS()
            tx_a_2 = mg.mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_2)

            mg = MOS()
            tx_b_1 = mg.mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_1)

            mg = MOS()
            tx_b_2 = mg.mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_2)

        tg = MOS()
        tp = tg.tap(self.transistor_array.unit_transistor)

        fill = MOS().fill(1, self.transistor_array.unit_transistor.nfin)

        # Define the interleaving array (aka array logic)
        if is_dual:
            interleave = self.interleave_pattern(self.n_row, self.n_col)
        else:
            interleave = [1]*(self.n_row*self.n_col)

        cnt = 0
        cnt_tap = 0
        rows = []
        for y in range(self.n_row):
            # tap row
            if y == 0:
                row = []

                row.append([fill, f't{cnt_tap}', {}, 1])
                cnt_tap += 1

                for _ in range(self.n_col):
                    row.append([tp, f't{cnt_tap}', tap_map, 1])
                    cnt_tap += 1
                rows.append(row)

                row.append([fill, f't{cnt_tap}', {}, 1])
                cnt_tap += 1

            row = []

            row.append([fill, f't{cnt_tap}', {}, 1])
            cnt_tap += 1

            for _ in range(self.n_col):
                pin_map = self.transistor_array.ports[interleave[cnt]]
                flip_x = 1
                
                if not is_dual:
                    tx = tx_a_1
                else:
                    if interleave[cnt] == 2:
                        if y % 2 == 0:
                            tx = tx_b_2
                        else:
                            tx = tx_b_1
                    else:
                        if y % 2 == 0:
                            tx = tx_a_1
                        else:
                            tx = tx_a_2
                
                row.append([tx, f'm{cnt}', pin_map, flip_x])
                cnt += 1

            row.append([fill, f't{cnt_tap}', {}, 1])
            cnt_tap += 1

            rows.append(row)

        # Stamp the instances
        self.place(rows)

        # Route
        self.route()

        self.terminals = self.removeDuplicates()


    def stamp_cell(self, template, instance_name, pin_map, x_offset, y_offset, flip_x):

        bbox = template['bbox']

        # bounding box as visual aid
        t = {'layer': 'Boundary', 'netName': None,
             'rect': [bbox[0]+x_offset, bbox[1]+y_offset, bbox[2]+x_offset, bbox[3]+y_offset]}
        self.terminals.append(t)

        if flip_x < 0:
            x_offset += bbox[2] - bbox[1]

        # append terminals
        for term in template['terminals']:
            t = {}
            r = term['rect'].copy()
            if flip_x < 0:
                t['rect'] = [x_offset-r[2], r[1]+y_offset, x_offset-r[0], r[3]+y_offset]
            else:
                t['rect'] = [x_offset+r[0], r[1]+y_offset, x_offset+r[2], r[3]+y_offset]

            t['layer'] = term['layer']
            t['netName'] = pin_map.get(term['netName'], None)
            self.terminals.append(t)


    def place(self, rows):
        x_offset = 0
        y_offset = 0

        x_offset += 0*self.pdk['Poly']['Pitch'] # whitespace for feol rules

        for row in rows:
            x_offset = 0
            for device in row:
                [cell, instance_name, pin_map, flip_x] = device
                self.stamp_cell(cell, instance_name, pin_map, x_offset, y_offset, flip_x)
                x_offset += cell['bbox'][2] - cell['bbox'][0]
            y_offset += cell['bbox'][3] - cell['bbox'][1]

        x_offset += 0*self.pdk['Poly']['Pitch'] # whitespace for feol rules

        self.bbox = transformation.Rect(*[0, 0, x_offset, y_offset])
        logger_func(f'bounding box: {self.bbox}')


    def route(self):
        self.join_wires(self.m1)
        self.join_wires(self.m2)

        def _stretch_m2_wires():
            x_min = self.bbox.urx
            x_max = self.bbox.lly 
            for term in self.terminals:
                if term['layer'] == self.m2.layer:
                    if term['rect'][0] < x_min:
                        x_min = term['rect'][0]
                    if term['rect'][2] > x_max:
                        x_max = term['rect'][2]
            for term in self.terminals:
                if term['layer'] == self.m2.layer:
                    if term['rect'][0] > x_min:
                        term['rect'][0] = x_min
                    if term['rect'][2] < x_max:
                        term['rect'][2] = x_max

        # M3
        self.terminals = self.removeDuplicates(silence_errors=True)
        if len(self.rd.opens) > 0:               
            open_pins = set()
            for t in self.rd.opens:
                open_pins.add(t[0])
           
            x_mid = (self.bbox.llx + self.bbox.urx)//2
            (c_idx, _) = self.m3.clg.inverseBounds(x_mid)
            c_idx = c_idx[0] - len(open_pins)//2

            def _find_y_bounds(pin, wire):
                y_min = self.bbox.ury
                y_max = self.bbox.lly
                for term in self.terminals:
                    if term['layer'] == wire.layer and term['netName'] in pin:
                        if term['rect'][1] < y_min:
                            y_min = term['rect'][1]
                        if term['rect'][3] > y_max:
                            y_max = term['rect'][3]
                return y_min, y_max
                
            y_min, y_max = _find_y_bounds(open_pins, self.m2)
            for pin in sorted(open_pins):
                if len(self.transistor_array.m)==1:
                    y_min, y_max = _find_y_bounds(pin, self.m2)
                (b1, b2) = self.m3.spg.inverseBounds(y_min)
                (e1, e2) = self.m3.spg.inverseBounds(y_max)
                if b1[0] + 1 == e2[0]:
                    b1 = (b1[0]-1, b1[1])  #  Satisfy min length
                self.addWire(self.m3, pin, None, c_idx, b1, e2)
                c_idx +=1

            self.drop_via(self.v2)

            self.terminals = self.removeDuplicates(silence_errors=True)
            if len(self.rd.opens) > 0:               
                _stretch_m2_wires()
                self.drop_via(self.v2)

        # Expose pins
        for term in self.terminals:
            if term['netName'] is not None and term['layer'] in ['M2', 'M3']:
                term['pin'] = term['netName']


    @staticmethod
    def validate_array(m, n_row, n_col):
        m = int(m)
        n_row = int(n_row)
        n_col = int(n_col)
        if n_row * n_col == m:
            return n_row, n_col
        else:
            y_sqrt = math.floor(math.sqrt(m))
            for y in range(y_sqrt, 0, -1):
                if y == 1:
                    return 1, m
                elif m % y == 0:
                    return y, m//y


    @staticmethod
    def interleave_pattern(n_row, n_col):
        """
        n_col odd:
            A B A
            B A B
        n_col even:
            A B A B 
            B A B A
        """
        if n_row * n_col > 1:
            assert (n_row * n_col) % 2 == 0, f'Odd number of transistors: {n_row}, {n_col}'
        if n_row == 1:
            assert n_col >= 2, 'Illegal combination'
        lst = []
        for y in range(n_row):
            if y % 2 == 0:
                lst.extend([k for k in islice(cycle([1, 2]), n_col)])
            else:
                lst.extend([k for k in islice(cycle([2, 1]), n_col)])
        return lst
