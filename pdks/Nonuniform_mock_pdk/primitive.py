import os
from itertools import cycle, islice, chain
from align.cell_fabric import transformation
from .canvas import CanvasPDK
from .gen_transistor import mos
from align.schema.transistor import Transistor, TransistorArray


class MOSGenerator(CanvasPDK):

    def __init__(self, *args, **kwargs):
        super().__init__()
        self.instantiated_cells = []

    # TODO: Eliminate this method, mos_array instead
    def addNMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(x_cells, y_cells, pattern, vt_type, ports, **parameters)

    # TODO: Eliminate this method, mos_array instead
    def addPMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(x_cells, y_cells, pattern, vt_type, ports, **parameters)

    # TODO: Eliminate this method. Pass align/schema/transistor.py/TransistorArray object to mos_array directly
    def mos_array_temporary_wrapper(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):

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

        unit_transistor = Transistor(device_type=device_type,
                                     nf=parameters[nf],
                                     nfin=4,
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

        transistor_array = TransistorArray(
            unit_transistor=unit_transistor,
            m=m,
            ports=p,
            n_rows=x_cells
        )
        # TODO: All of above goes away when TransistorArray is passed to mos_array as shown below
        #################################################################################################

        self.mos_array(transistor_array, **parameters)

    def mos_array(self, transistor_array: TransistorArray, **parameters):

        assert len(transistor_array.m) <= 2, f'Arrays of more than 2 devices not supported yet'

        # Generate leaf cells
        tx = mos(transistor_array.unit_transistor)

        # Define the interleaving array (aka array logic)
        n_row, n_col = self._calculate_row_col(transistor_array)

        interleave = self.interleave_pattern(transistor_array, n_row, n_col)
        print(interleave)

        cnt = 0
        rows = []
        for y in range(n_row):
            row = []
            for x in range(n_col):
                pin_map = transistor_array.ports.get(interleave[cnt], transistor_array.ports[1])
                flip_x = 1
                row.append([tx, f'i{cnt}', pin_map, flip_x])
                cnt += 1
            rows.append(row)

        # Stamp the instances
        self.place(rows)

        # Route
        self.route()

        self.computeBbox()

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

        # Cells listed below has to be instantiated during/after importing layout to Virtuoso
        self.instantiated_cells.append([instance_name, (x_offset, y_offset, flip_x, 1), template['instance']])

    def place(self, rows):
        # keep record of what x, y, sx, sy the instance is stamped
        x_offset = y_offset = 0
        for row in rows:
            x_offset = 0
            for device in row:
                [cell, instance_name, pin_map, flip_x] = device
                self.stamp_cell(cell, instance_name, pin_map, x_offset, y_offset, flip_x)
                x_offset += cell['bbox'][2] - cell['bbox'][0]
            y_offset += cell['bbox'][3] - cell['bbox'][1]

        self.bbox = transformation.Rect(*[0, 0, x_offset, y_offset])
        print(self.bbox)

    def route(self):
        pass

    @staticmethod
    def _calculate_row_col(transistor_array: TransistorArray):
        m = 0
        for _, v in transistor_array.m.items():
            m += v
        assert m % transistor_array.n_rows == 0, \
            f'Illegal number of rows {transistor_array.n_rows} for {m} devices in total'
        return transistor_array.n_rows, m // transistor_array.n_rows

    @staticmethod
    def interleave_pattern(transistor_array, n_row, n_col):
        lst = []
        if len(transistor_array.m) < 2:
            for y in range(n_row):
                lst.extend([0]*n_col)
        else:
            m = (n_col * n_row) // 2
            if m % 2 == 0:  # even
                for y in range(n_row):
                    if y % 2 == 0:
                        lst.extend([k for k in islice(cycle([1, 2]), n_col)])
                    else:
                        lst.extend([k for k in islice(cycle([2, 1]), n_col)])
            else:  # odd
                lst = [1, 2] * m
        return lst


def test_one():
    mg = MOSGenerator()
    ports = {'SA': [('M1', 'S')], 'DA': [('M1', 'D')], 'GA': [('M1', 'G')]}
    parameters = {'m': 4, 'nf': 2, 'real_inst_type': 'n'}
    mg.addNMOSArray(2, 1, 1, None, ports, **parameters)
    fn = os.path.join(os.environ['ALIGN_HOME'], 'Viewer/INPUT/test_primitive_one.json')
    with open(fn, "wt") as fp:
        mg.writeJSON(fp, draw_grid=False, run_drc=False, run_pex=False, postprocess=True)


def test_two():
    mg = MOSGenerator()
    ports = {'S': [('M1', 'S'), ('M2', 'S')],
             'DA': [('M1', 'D')], 'DB': [('M2', 'D')],
             'GA': [('M1', 'G')], 'GB': [('M2', 'G')]
             }
    parameters = {'m': 4, 'stack': 4, 'real_inst_type': 'n'}
    mg.addNMOSArray(2, 1, 1, None, ports, **parameters)
    fn = os.path.join(os.environ['ALIGN_HOME'], 'Viewer/INPUT/test_primitive_two.json')
    with open(fn, "wt") as fp:
        mg.writeJSON(fp, draw_grid=False, run_drc=False, run_pex=False, postprocess=True, )


test_one()
test_two()
