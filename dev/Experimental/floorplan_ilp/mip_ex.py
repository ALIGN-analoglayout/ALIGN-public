
from mip import Model, MINIMIZE, xsum, CBC, OptimizationStatus, BINARY, INTEGER

from itertools import product, combinations
from collections import defaultdict
import pytest

import plotly.graph_objects as go


def wire_length(m, *, sizes, wires):
    for wire_name, terminals in wires:

        for tag, axis in product(['ll', 'ur'], ['x', 'y']):
            m.add_var(name=f'{wire_name}_{tag}{axis}')

        for instance, bbox in terminals:
            size = dict(zip("xy", sizes[instance]))
            for (tag, axis), offset in zip(product(['ll', 'ur'], ['x', 'y']), bbox):
                P, Q = size[axis] - 2*offset, offset
                eqn = P * m.var_by_name(f'{instance}_f{axis.upper()}') + Q + m.var_by_name(f'{instance}_ll{axis}')
                m += eqn <= m.var_by_name(f'{wire_name}_ur{axis}')
                m += m.var_by_name(f'{wire_name}_ll{axis}') <= eqn

    hpwl = m.add_var(name='hpwl')

    m += xsum(m.var_by_name(f'{wire_name}_ur{axis}') for wire_name, _ in wires for axis in ['x', 'y']) - \
        xsum(m.var_by_name(f'{wire_name}_ll{axis}') for wire_name, _ in wires for axis in ['x', 'y']) == hpwl


def floorplan(m, *, sizes, fp, symmetrize=False, order=True):

    if order:
        for row in fp:
            m += m.var_by_name('llx') <= m.var_by_name(f'{row[0]}_llx')
            m += m.var_by_name(f'{row[-1]}_urx') <= m.var_by_name('urx')

            for l, r in zip(row[:-1], row[1:]):
                m += m.var_by_name(f'{l}_urx') <= m.var_by_name(f'{r}_llx')
    else:
        for row in fp:
            for cell in row:
                m += m.var_by_name('llx') <= m.var_by_name(f'{cell}_llx')
                m += m.var_by_name(f'{cell}_urx') <= m.var_by_name('urx')

            Mx = sum(size[0] for _, size in sizes.items())
            My = sum(size[1] for _, size in sizes.items())

            # four BINARYs for each pair in the row
            for a, b in combinations(row, 2):
                below = m.add_var(name=f'{a}_below_{b}', var_type=BINARY)
                above = m.add_var(name=f'{a}_above_{b}', var_type=BINARY)
                left_of = m.add_var(name=f'{a}_left_of_{b}', var_type=BINARY)
                right_of = m.add_var(name=f'{a}_right_of_{b}', var_type=BINARY)
                m += below + above + left_of + right_of == 1

                m += m.var_by_name(f'{a}_urx') <= m.var_by_name(f'{b}_llx') + Mx - Mx*left_of
                m += m.var_by_name(f'{b}_urx') <= m.var_by_name(f'{a}_llx') + Mx - Mx*right_of

                m += m.var_by_name(f'{a}_ury') <= m.var_by_name(f'{b}_lly') + My - My*below
                m += m.var_by_name(f'{b}_ury') <= m.var_by_name(f'{a}_lly') + My - My*above

    # Between rows
    between_rows = [m.add_var(name=f'between_rows_{i}') for i in range(len(fp)-1)]

    for i, row in enumerate(fp):
        if i == 0:
            for cell in row:
                m += m.var_by_name(f'{cell}_ury') <= m.var_by_name('ury')
        elif i == len(fp) - 1:
            for cell in row:
                m += m.var_by_name('lly') <= m.var_by_name(f'{cell}_lly')

        if i < len(between_rows):
            for cell in row:
                m += between_rows[i] <= m.var_by_name(f'{cell}_lly')
        if i > 0:
            for cell in row:
                m += m.var_by_name(f'{cell}_ury') <= between_rows[i-1]

    if symmetrize:
        line_of_symmetry = m.add_var(name='line_of_symmetry')

        for row in fp:
            if len(row) % 2 == 1:
                cell = row[len(row)//2]
                m += m.var_by_name(f'{cell}_llx') + m.var_by_name(f'{cell}_urx') == 2*line_of_symmetry

            for i in range(len(row)//2):
                cell_l = row[i]
                cell_r = row[len(row)-1-i]
                m += m.var_by_name(f'{cell_l}_llx') + m.var_by_name(f'{cell_r}_urx') == 2*line_of_symmetry

                # flips must be different
                m += m.var_by_name(f'{cell_l}_fX') + m.var_by_name(f'{cell_r}_fX') == 1


def place(*, sizes, wires, place_on_grid, fp, symmetrize=False, order=True, constraints=None, objective=None):
    m = Model(sense=MINIMIZE, solver_name=CBC)
    # set to one to see more progress output with the solver
    m.verbose = 0

    for k, _ in sizes.items():
        for tag in ['llx', 'lly', 'urx', 'ury']:
            m.add_var(name=f'{k}_{tag}', lb=0)

        for tag in ['X', 'Y']:
            f = m.add_var(name=f'{k}_f{tag}', var_type=BINARY)

        size = dict(zip("xy", sizes[k]))

        for axis in "xy":
            m += m.var_by_name(f'{k}_ll{axis}') + size[axis] == m.var_by_name(f'{k}_ur{axis}')

        if k in place_on_grid:
            for d in place_on_grid[k]:
                axis = d['axis']
                pitch = d['pitch']
                f = m.var_by_name(f'{k}_f{axis.upper()}')

                if True:  # Refactored version
                    offset_scalings = defaultdict(list)
                    offset_variables = list()
                    for term in d['ored_terms']:
                        offsets = term['offsets']
                        scalings = term['scalings']
                        assert set(scalings) in [{1}, {-1}, {-1, 1}]
                        for offset in offsets:
                            assert offset not in offset_scalings, "Check not required, added for test_duplicate_offset"
                            offset_scalings[offset].extend(scalings)
                    for offset, scalings in offset_scalings.items():
                        var = m.add_var(var_type=BINARY)
                        offset_variables.append((offset, var))
                        if set(scalings) == {1}:
                            m += var + f <= 1
                        elif set(scalings) == {-1}:
                            m += var <= f
                    m += xsum(var[1] for var in offset_variables) == 1
                    grid = m.add_var(name=f'{k}_grid_{axis}', var_type=INTEGER, lb=0)
                    origin = grid*pitch + xsum(v[0]*v[1] for v in offset_variables)
                    m += origin - size[axis] * f == m.var_by_name(f'{k}_ll{axis}')

                else:
                    one_hots = defaultdict(list)
                    for dd in d['ored_terms']:
                        offsets = dd['offsets']
                        scalings = dd['scalings']
                        assert set(scalings) == {-1} or set(scalings) == {1} or set(scalings) == {-1, 1}
                        one_hots[frozenset(set(scalings))].extend(offsets)
                    count = sum(len(v) for _, v in one_hots.items())
                    assert count == len(set(o for _, v in one_hots.items() for o in v))
                    # Don't use any variables if there is only one offset
                    if count == 1:
                        for scalings_fs, v in one_hots.items():
                            one_hots[scalings_fs] = [(o, 1) for o in v]
                    else:
                        for scalings_fs, v in one_hots.items():
                            one_hots[scalings_fs] = [(o, m.add_var(var_type=BINARY)) for o in v]
                        m += xsum(b for _, v in one_hots.items() for _, b in v) == 1
                    # force flipping
                    for scalings_fs, pairs in one_hots.items():
                        if scalings_fs == {-1}:
                            for _, b in pairs:
                                m += b <= f
                        if scalings_fs == {1}:
                            for _, b in pairs:
                                m += f <= 1 - b
                    grid = m.add_var(name=f'{k}_grid_{axis}', var_type=INTEGER)
                    origin = grid * pitch + xsum(c*b for _, v in one_hots.items() for c, b in v)
                    m += origin - size[axis] * f == m.var_by_name(f'{k}_ll{axis}')

    for tag in ['llx', 'lly', 'urx', 'ury']:
        m.add_var(name=f'{tag}')

    floorplan(m, sizes=sizes, fp=fp, symmetrize=symmetrize, order=order)
    wire_length(m, sizes=sizes, wires=wires)

    z = m.add_var('z')

    if objective is None:
        objective = {'urx': 1, 'ury': 1, 'hpwl': 1}

    if constraints is None:
        constraints = {}

    m += xsum(m.var_by_name(k)*v for k, v in objective.items()) == z

    for k, v in constraints.items():
        m += m.var_by_name(k) <= v

    m.objective += z

    m.write('model.lp')

    status = m.optimize(max_seconds_same_incumbent=60.0)
    if status == OptimizationStatus.OPTIMAL:
        print(f'optimal solution found: cost={m.objective_value}')
    elif status == OptimizationStatus.FEASIBLE:
        print(f'solution with cost {m.objective_value} current lower bound: {m.objective_bound}')
    else:
        raise Exception('No solution to ILP')

    if status == OptimizationStatus.OPTIMAL or status == OptimizationStatus.FEASIBLE:
        print('Solution:')
        for v in m.vars:
            print('\t', v.name, v.x)
        print(f'Number of solutions: {m.num_solutions}')

    return m

def draw(m, *, fp, wires):
    xs, ys = [], []

    def add_point(x, y):
        xs.append(x)
        ys.append(y)

    def add_space():
        xs.append(None)
        ys.append(None)

    def add_rect(xll, yll, xur, yur):
        add_point(xll, yll)
        add_point(xur, yll)
        add_point(xur, yur)
        add_point(xll, yur)
        add_point(xll, yll)

    fig = go.Figure()

    for row in fp:
        for cell in row:
            xs.clear()
            ys.clear()
            llx, lly = m.var_by_name(f'{cell}_llx').x, m.var_by_name(f'{cell}_lly').x
            urx, ury = m.var_by_name(f'{cell}_urx').x, m.var_by_name(f'{cell}_ury').x
            add_rect(llx, lly, urx, ury)
            add_space()
            fX, fY = m.var_by_name(f'{cell}_fX').x, m.var_by_name(f'{cell}_fY').x
            fig.add_trace(go.Scatter(x=xs, y=ys, fill='toself', mode='lines', name=f'{cell} fX={fX:.0f} fY={fY:.0f}'))

    for wire_name, _ in wires:
        llx, lly = m.var_by_name(f'{wire_name}_llx').x, m.var_by_name(f'{wire_name}_lly').x
        urx, ury = m.var_by_name(f'{wire_name}_urx').x, m.var_by_name(f'{wire_name}_ury').x
        xs.clear()
        ys.clear()
        add_rect(llx, lly, urx, ury)
        add_space()
        fig.add_trace(go.Scatter(x=xs, y=ys, fill='toself', mode='lines', line={'color': 'RoyalBlue'}, name=f'{wire_name}'))
        

    # fig.update_xaxes(showticklabels=False)
    # fig.update_yaxes(showticklabels=False)

    fig.update_yaxes(
        scaleanchor = "x",
        scaleratio = 1
    )

    fig.show()


def test_simple():

    place_on_grid = {'x': [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [2], 'scalings': [-1, 1]}]}]}
    sizes = {'x': (1, 1), 'y': (1, 1), 'z': (1, 1), 'a': (1, 1), 'b': (1, 1)}
    wires = [('w', [('x', (.25, .25, .25, .25)), ('y', (.75, .75, .75, .75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b']
          ]

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

    draw(m, fp=fp, wires=wires)

    assert m.var_by_name('hpwl').x == 0.5


def test_large():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h'],
          ['i', 'j', 'k', 'l']
          ]
    sizes = {nm: (2, 2) for row in fp for nm in row}

    place_on_grid = {nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          {'axis': 'x', 'pitch': 1,  'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          ] for row in fp for nm in row}

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

    draw(m, fp=fp, wires=wires)

    assert m.var_by_name('hpwl').x == 2.0

    assert m.var_by_name('i_fY').x == 0
    assert m.var_by_name('e_fY').x == 1
    assert m.var_by_name('a_fY').x == 0
    assert m.var_by_name('x_fY').x == 1


def test_large_symmetrize():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h'],
          ['i', 'j', 'k', 'l']
          ]
    sizes = {nm: (2, 2) for row in fp for nm in row}

    place_on_grid = {nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          {'axis': 'x', 'pitch': 1,  'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          ] for row in fp for nm in row}

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, symmetrize=True)

    draw(m, fp=fp, wires=wires)


    assert m.var_by_name('hpwl').x == 2.0

    assert m.var_by_name('i_fY').x == 0
    assert m.var_by_name('e_fY').x == 1
    assert m.var_by_name('a_fY').x == 0
    assert m.var_by_name('x_fY').x == 1

def test_large_noorder_3_wide():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h']
    ]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = {nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          {'axis': 'x', 'pitch': 1,  'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]}]},
                          ] for row in fp for nm in row}

    constraints = { 'urx': 3 }

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, order=False, constraints=constraints)

    draw(m, fp=fp, wires=wires)

def test_large_noorder_6_tall():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h']
    ]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                           {'axis': 'x', 'pitch': 1, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                          ] for row in fp for nm in row }

    constraints = { 'ury': 6 }

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, order=False, constraints=constraints)

    draw(m, fp=fp, wires=wires)

def test_large_noorder_5_tall():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h']
    ]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                           {'axis': 'x', 'pitch': 1, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                          ] for row in fp for nm in row }

    constraints = { 'ury': 5 }

    with pytest.raises(Exception) as exc_info:
        m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, order=False, constraints=constraints)
        draw(m, fp=fp, wires=wires)


def test_snake_no_order():

    wires = [('w0', [('w', (.25,.25,.25,.25)), ('x', (1.75,1.75,1.75,1.75))]),
             ('w1', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))]),
             ('w2', [('y', (.25,.25,.25,.25)), ('z', (1.75,1.75,1.75,1.75))]),
             ('w3', [('z', (.25,.25,.25,.25)), ('d', (1.75,1.75,1.75,1.75))]),
             ('w4', [('d', (.25,.25,.25,.25)), ('c', (1.75,1.75,1.75,1.75))]),
             ('w5', [('c', (.25,.25,.25,.25)), ('b', (1.75,1.75,1.75,1.75))]),
             ('w6', [('b', (.25,.25,.25,.25)), ('a', (1.75,1.75,1.75,1.75))]),
             ('w7', [('a', (.25,.25,.25,.25)), ('e', (1.75,1.75,1.75,1.75))]),
             ('w8', [('e', (.25,.25,.25,.25)), ('f', (1.75,1.75,1.75,1.75))]),
             ('w9', [('f', (.25,.25,.25,.25)), ('g', (1.75,1.75,1.75,1.75))]),
             ('wa', [('g', (.25,.25,.25,.25)), ('h', (1.75,1.75,1.75,1.75))])]
             
    fp = [['w', 'x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h']
    ]

    sizes = { nm: (2,2) for row in fp for nm in row }

    if True:
        place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                               {'axis': 'x', 'pitch': 1, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                              ] for row in fp for nm in row }
    else:
        place_on_grid = {}

    constraints = {'ury': 6}
    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, order=False, constraints=constraints)
    draw(m, fp=fp, wires=wires)

def test_snake_order():

    wires = [('w0', [('w', (.25,.25,.25,.25)), ('x', (1.75,1.75,1.75,1.75))]),
             ('w1', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))]),
             ('w2', [('y', (.25,.25,.25,.25)), ('z', (1.75,1.75,1.75,1.75))]),
             ('w3', [('z', (.25,.25,.25,.25)), ('d', (1.75,1.75,1.75,1.75))]),
             ('w4', [('d', (.25,.25,.25,.25)), ('c', (1.75,1.75,1.75,1.75))]),
             ('w5', [('c', (.25,.25,.25,.25)), ('b', (1.75,1.75,1.75,1.75))]),
             ('w6', [('b', (.25,.25,.25,.25)), ('a', (1.75,1.75,1.75,1.75))]),
             ('w7', [('a', (.25,.25,.25,.25)), ('e', (1.75,1.75,1.75,1.75))]),
             ('w8', [('e', (.25,.25,.25,.25)), ('f', (1.75,1.75,1.75,1.75))]),
             ('w9', [('f', (.25,.25,.25,.25)), ('g', (1.75,1.75,1.75,1.75))]),
             ('wa', [('g', (.25,.25,.25,.25)), ('h', (1.75,1.75,1.75,1.75))])]
             
    fp = [['w', 'x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h']
    ]
    sizes = { nm: (2,2) for row in fp for nm in row }

    if True:
        place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                               {'axis': 'x', 'pitch': 1, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                              ] for row in fp for nm in row }
    else:
        place_on_grid = {}

    constraints = {}
    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid, order=True, constraints=constraints)
    draw(m, fp=fp, wires=wires)




def test_duplicate_offset():
    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y']]
    sizes = {nm: (2, 2) for row in fp for nm in row}

    place_on_grid = {nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [0], 'scalings': [-1, 1]},
                                                                   {'offsets': [0], 'scalings': [1]}]}
                          ] for row in fp for nm in row}

    with pytest.raises(Exception, match='assert') as _:
        place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)


def test_bad_scaling():
    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (1.75,1.75,1.75,1.75))])]
    fp = [['x', 'y']]
    sizes = {nm: (2, 2) for row in fp for nm in row}

    place_on_grid = {nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [0], 'scalings': [-1, 1, 2]}]}
                          ] for row in fp for nm in row}

    with pytest.raises(Exception, match='assert') as _:
        place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)


if __name__ == "__main__":
    test_simple()
