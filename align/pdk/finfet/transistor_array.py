import os
import math
import json
from itertools import cycle, islice
from collections import defaultdict
from align.cell_fabric import transformation
from align.schema.transistor import Transistor, TransistorArray
from . import CanvasPDK, MOS
from .gen_param import construct_sizes_from_exact_patterns 

import logging
logger = logging.getLogger(__name__)
logger_func = logger.debug


class MOSGenerator(CanvasPDK):

    def __init__(self, *args, **kwargs):
        self.primitive_constraints = kwargs.get('primitive_constraints', [])

        super().__init__()

        self.pattern_template = None
        self.PARTIAL_ROUTING = False
        self.single_device_connect_m1 = True
        self.exact_patterns = None
        self.exact_patterns_d = None
        for const in self.primitive_constraints:
            if const.constraint == 'generator':
                if const.parameters is not None:
                    self.pattern_template = const.parameters.get('pattern_template')
                    self.PARTIAL_ROUTING = const.parameters.get('PARTIAL_ROUTING', False)
                    self.single_device_connect_m1 = const.parameters.get('single_device_connect_m1', True)
                    self.exact_patterns = const.parameters.get('exact_patterns')

                    if self.exact_patterns is not None:
                        self.exact_patterns_d = construct_sizes_from_exact_patterns(self.exact_patterns)

                    legal_keys = set(['pattern_template', 'PARTIAL_ROUTING', 'single_device_connect_m1', 'exact_patterns', 'legal_sizes'])
                    for k in const.parameters.keys():
                        assert k in legal_keys, (k, legal_keys)


        if os.getenv('PARTIAL_ROUTING', None) is not None:
            self.PARTIAL_ROUTING = True

        #logger.info(f'pattern_template: {self.pattern_template} PARTIAL_ROUTING: {self.PARTIAL_ROUTING} single_device_connect_m1: {self.single_device_connect_m1}')

        if self.PARTIAL_ROUTING:
            if not hasattr(self, 'metadata'):
                self.metadata = dict()
            self.metadata['partially_routed_pins'] = {}

        # Inject constraints for testing purposes
        place_on_grid = os.getenv('PLACE_ON_GRID', None)
        if place_on_grid is not None:
            place_on_grid = json.loads(place_on_grid)
            if not hasattr(self, 'metadata'):
                self.metadata = dict()
            self.metadata['constraints'] = place_on_grid['constraints']

    def addNMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.addMOSArray(x_cells, y_cells, pattern, vt_type, ports, **parameters)

    def addPMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.addMOSArray(x_cells, y_cells, pattern, vt_type, ports, **parameters)

    def addMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):

        logger_func(f'x_cells={x_cells}, y_cells={y_cells}, pattern={pattern}, ports={ports}, parameters={parameters}')

        parameters = {k.lower(): v for k, v in parameters.items()}  # Revert all parameters to lower case

        #################################################################################################
        assert pattern in {0, 1, 2}, f'This primitive cannot be generated with this PDK. Unknown pattern {pattern}'

        for key in ['m', 'real_inst_type']:
            assert key in parameters, f'Missing transistor parameter {key}'
        assert 'nf' or 'stack' in parameters, 'Missing transistor parameter nf or stack'

        m = int(parameters['m'])

        if 'stack' in parameters and int(parameters['stack']) > 1:
            nf = int(parameters['stack'])
            device_type = 'stack'
        elif 'nf' in parameters and int(parameters['nf']) > 1:
            nf = int(parameters['nf'])
            device_type = 'parallel'
        else:
            assert False, f'Either nf>1 or stack>1 parameter should be defined {parameters}'

        if 'w' in parameters:
            nfin = int(float(parameters['w']) * 1e10) // self.pdk['Fin']['Pitch']
            # Divide w by nf for parallel devices
            if device_type == 'parallel':
                nfin = nfin // nf
        elif 'nfin' in parameters:
            nfin = parameters['nfin']
        else:
            assert False, f'Either nfin or w parameter should be defined {parameters}'

        unit_transistor = Transistor(device_type=device_type,
                                     nf=nf,
                                     nfin=nfin,
                                     model_name=parameters['real_inst_type'].lower())

        def find_ports(p, i):
            res = {vv: k for k, v in p.items() for kk, vv in v if kk == i}
            logger.debug(f'find_ports: p {p} i {i} res {res}')
            return res

        element_names = sorted({c[0] for mc in ports.values() for c in mc})

        p1 = find_ports(ports, element_names[0])
        port_arr = {1: p1}
        mult_arr = {1: m}
        if len(element_names) > 1:
            p2 = find_ports(ports, element_names[1])
            if len(p2) > 1:
                port_arr[2] = p2
                mult_arr[2] = m
        self.transistor_array = TransistorArray(
            unit_transistor=unit_transistor,
            m=mult_arr,
            ports=port_arr,
            n_rows=y_cells
        )
        #################################################################################################
        m = 2*m if pattern > 0 else m
        self.n_row, self.n_col = self.validate_array(m, y_cells, x_cells)
        logger_func(f'x_cells={self.n_col}, y_cells={self.n_row} after legalization')

        if self.n_row * self.n_col != m:
            assert False, f'x_cells {self.n_row} by y_cells {self.n_col} not equal to m {m}'

        self.ports = ports
        self.mos_array()

        # bounding box as visual aid
        if parameters['real_inst_type'].lower().startswith('p'):
            self.terminals.insert(0, {'layer': 'Nwell', 'netName': None, 'netType': 'drawing', 'rect': self.bbox.toList()})

    def mos_array(self):

        assert len(self.transistor_array.m) <= 2, 'Arrays of more than 2 devices not supported yet'

        is_dual = len(self.transistor_array.m) == 2
        tap_map = {'B': self.transistor_array.ports[1].get('B','B')}


        '''
            if PARTIAL_ROUTING:
                route single transistor primitives up to m1 excluding gate
                route double transistor primitives up to m2
        '''

        # Assign M2 tracks to prevent adjacent V2 violation
        track_pattern_1 = {'G': [6], 'S': [4], 'D': [2]}
        track_pattern_2 = {'G': [5], 'S': [3], 'D': [1]}

        if is_dual:
            for tgt, srcs in [('G',['G','S']),('S',['S','D']),('D',['D'])]:
                for src in srcs:
                    if self.transistor_array.ports[2][tgt] == self.transistor_array.ports[1][src]:
                        track_pattern_2[tgt] = track_pattern_1[src]
                        break

            # Alternate m2 tracks for device A and device B for improved matching
            tx_2 = MOS().mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_2)
        elif self.PARTIAL_ROUTING:
            if self.single_device_connect_m1:
                track_pattern_1 = {'G': [6]}

        tx_1 = MOS().mos(self.transistor_array.unit_transistor, track_pattern=track_pattern_1)


        tp = MOS().tap(self.transistor_array.unit_transistor)
        fill = MOS().fill(1, self.transistor_array.unit_transistor.nfin)


        # Define the interleaving array (aka array logic)
        if is_dual:
            if self.exact_patterns_d is not None:
                k = self.n_col//2, self.n_row
                assert k in self.exact_patterns_d, (k, self.exact_patterns_d)
                interleave_array = self.interleave_pattern(self.n_row, self.n_col, pattern_template=self.exact_patterns_d[k])
            elif self.pattern_template is not None:
                interleave_array = self.interleave_pattern(self.n_row, self.n_col, pattern_template=self.pattern_template)                
            else:
                interleave_array = self.interleave_pattern(self.n_row, self.n_col)
        else:
            # Probably want to be able to change the singleton pattern
            interleave_array = self.interleave_pattern(self.n_row, self.n_col, pattern_template=["A"])

        cnt_tap = 0
        def add_tap(row, obj, tbl, flip_x):
            nonlocal cnt_tap
            row.append([obj, f't{cnt_tap}', tbl, flip_x])
            cnt_tap += 1

        rows = []

        # tap row
        row = []
        add_tap(row, fill, {}, 1)
        for _ in range(self.n_col):
            add_tap(row, tp, tap_map, 1)
        rows.append(row)
        add_tap(row, fill, {}, 1)

        tr = {'A': (1,  1),
              'a': (1, -1),
              'B': (2,  1),
              'b': (2, -1)}

        for y in range(self.n_row):
            row = []
            add_tap(row, fill, {}, 1)
            for x in range(self.n_col):
                port_idx, flip_x = tr[interleave_array[y][x]]

                pin_map = self.transistor_array.ports[port_idx]

                tx = tx_1
                if is_dual:
                    if port_idx == 2:
                        tx = tx_2 if y % 2 == 0 else tx_1
                    else:
                        tx = tx_1 if y % 2 == 0 else tx_2

                #row.append([tx, f'm{y*self.n_col+x}', pin_map, flip_x])
                row.append([tx, f'm{y}_{x}', pin_map, flip_x])

            add_tap(row, fill, {}, 1)
            rows.append(row)

        # Stamp the instances
        self.place(rows)

        if not self.PARTIAL_ROUTING:
            self.route()
            self.terminals = self.removeDuplicates()
        else:
            if self.single_device_connect_m1 and not is_dual:
                self.join_wires(self.m1)
            self.join_wires(self.m2)
            self.terminals = self.removeDuplicates(silence_errors=True)

            replacements = {}

            counters = defaultdict(int)
            for net_name, open_groups in self.rd.opens:
                for open_group in open_groups:
                    counters[net_name] += 1
                    new_name = f'{net_name}__{counters[net_name]}'
                    assert 'partially_routed_pins' in self.metadata
                    self.metadata['partially_routed_pins'][new_name] = net_name
                    for layer, rect in open_group:
                        replacements[(layer, tuple(rect))] = new_name

            for term in self.terminals:
                new_name = replacements.get((term['layer'], tuple(term['rect'])))
                if new_name is not None:
                    term.update({'netName': new_name, 'netType': 'pin'})

            # Expose pins
            self._expose_pins()

    def stamp_cell(self, template, instance_name, pin_map, x_offset, y_offset, flip_x):

        bbox = template['bbox']

        # bounding box as visual aid
        t = {'layer': 'Boundary', 'netName': None, 'netType': 'drawing',
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
            t['netType'] = term['netType']
            self.terminals.append(t)

    def place(self, rows):
        x_offset = 0
        y_offset = 0

        x_offset += 0*self.pdk['Poly']['Pitch']  # whitespace for feol rules

        for row in rows:
            x_offset = 0
            for device in row:
                [cell, instance_name, pin_map, flip_x] = device
                self.stamp_cell(cell, instance_name, pin_map, x_offset, y_offset, flip_x)
                x_offset += cell['bbox'][2] - cell['bbox'][0]
            y_offset += cell['bbox'][3] - cell['bbox'][1]

        x_offset += 0*self.pdk['Poly']['Pitch']  # whitespace for feol rules

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
                if len(self.transistor_array.m) == 1:
                    y_min, y_max = _find_y_bounds(pin, self.m2)
                (b1, b2) = self.m3.spg.inverseBounds(y_min)
                (e1, e2) = self.m3.spg.inverseBounds(y_max)
                if b1[0] + 1 == e2[0]:
                    b1 = (b1[0]-1, b1[1])  # Satisfy min length
                self.addWire(self.m3, pin, c_idx, b1, e2)
                c_idx += 1

            self.drop_via(self.v2)

            self.terminals = self.removeDuplicates(silence_errors=True)
            if len(self.rd.opens) > 0:
                _stretch_m2_wires()
                self.drop_via(self.v2)

        if False:
            # Expose pins
            for term in self.terminals:
                if term['netName'] is not None and term['layer'] in ['M2', 'M3']:
                    term['netType'] = 'pin'
        else:
            self._expose_pins()

    def _expose_pins(self):
        net_layers = defaultdict(set)
        for term in self.terminals:
            if term['netName'] is not None and term['layer'].startswith('M'):
                net_layers[term['netName']].add(term['layer'])

        for name, layers in net_layers.items():
            max_layer = max(layers)
            for term in self.terminals:
                nm, ly = term['netName'], term['layer']
                if nm is not None and nm == name:
                    if ly == max_layer:
                        term['netType'] = 'pin'
                    else:
                        term['netType'] = 'drawing'

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
    def interleave_pattern(n_row, n_col, *, pattern_template=["AB","BA"]):
        """
        (lower case means flipped around the y-axis (mirrored in x))
            A B
            B A
        or
            A a B b
            B b A b
        or (radhad)
            A b B a
            B a A b
        """
        assert len(pattern_template) > 0
        return [list(islice(cycle(pattern_template[y%len(pattern_template)]), n_col)) for y in range(n_row)]
