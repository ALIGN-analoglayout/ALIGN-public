import os
import json
import math
import pathlib
import importlib
from itertools import cycle, islice, chain
from align.cell_fabric import transformation
from canvas import NonuniformCanvas
from align.schema import Transistor, TransistorArray
from gen_transistor import mos


class MOSGenerator(NonuniformCanvas):

    def __init__(self, *args, **kwargs):
        super().__init__()

    # TODO: Eliminate this method, mos_array instead
    def addNMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(self, x_cells, y_cells, pattern, vt_type, ports, **parameters)

    # TODO: Eliminate this method, mos_array instead
    def addPMOSArray(self, x_cells, y_cells, pattern, vt_type, ports, **parameters):
        self.mos_array_temporary_wrapper(self, x_cells, y_cells, pattern, vt_type, ports, **parameters)

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
                                     nf=nf,
                                     nfin=4,
                                     model_name=parameters['real_inst_type'])

        if pattern == 0:
            m = {1: parameters['m']}
        elif pattern == 1:
            m = {1: parameters['m'], 2: parameters['m']}

        def find_ports(p, i):
            d = {}
            for (k, v) in p.items():
                for t in v:
                    if t[0] == i:
                        d[t[1]] = k
            return d
        p1 = find_ports(ports, 'M1')
        p2 = find_ports(ports, 'M1')

        transistor_array = TransistorArray(
            unit_transistor = unit_transistor,
            m = m,
            ports = {1:p1, 2:p2},
            n_rows = x_cells
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

        interleave = self.interleave_pattern(n_row, n_col)

        cnt = 0
        rows = []
        for y in range(n_row):
            row = []
            for x in range(n_col):
                pin_map = transistor_array.ports.get(interleave[cnt], transistor_array.ports[1])
                flip = [1, 1]
                row.append([tx, pin_map, flip])
            rows.append(row)

        # Stamp the instances
        self.stamp_on_canvas(rows)

        # Route
        self.route()

        self.computeBbox()

    def stamp_on_canvas(self, unit_transistor):
        # keep record of what x, y, sx, sy the instance is stamped
        pass

    def route(self):
        pass

    @staticmethod
    def _calculate_row_col(transistor_array: TransistorArray):
        m = 0
        for _, v in transistor_array.m:
            m += v
        assert m % transistor_array.n_rows == 0, \
            f'Illegal number of rows {transistor_array.n_rows} for {m} devices in total'
        return transistor_array.n_rows, m // transistor_array.n_rows

    @staticmethod
    def interleave_pattern(n_row, n_col):
        m = (n_col * n_row) // 2
        if m % 2 == 0:  # even
            lst = []
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
    ports = {}
    parameters = {}
    mg.addNMOSArray(4, _, _, _, ports, **parameters)

