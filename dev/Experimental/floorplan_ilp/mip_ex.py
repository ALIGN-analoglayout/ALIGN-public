
from mip import *
from itertools import product
from collections import defaultdict
import pytest


def wire_length(m, sizes, wires):
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


def floorplan(m, sizes, fp):

    for k, v in sizes.items():
        m += m.var_by_name(f'{k}_llx') + v[0] == m.var_by_name(f'{k}_urx')
        m += m.var_by_name(f'{k}_lly') + v[1] == m.var_by_name(f'{k}_ury')

    

    for i, row in enumerate(fp):
        m += m.var_by_name('llx') <= m.var_by_name(f'{row[0]}_llx') 
        m += m.var_by_name(f'{row[-1]}_urx') <= m.var_by_name('urx')

        if i == 0:
            for cell in row:
                m += m.var_by_name(f'{cell}_ury') <= m.var_by_name('ury')
        if i == len(fp) - 1:
             for cell in row:
                m += m.var_by_name('lly') <= m.var_by_name(f'{cell}_lly')       

    # Between rows
    between_rows = [m.add_var(name=f'between_rows_{i}') for i in range(len(fp)-1)]

    for i, row in enumerate(fp):
        if i < len(between_rows):
            for cell in row:
                m += between_rows[i] <= m.var_by_name(f'{cell}_lly')
        if i > 0:
            for cell in row:
                m += m.var_by_name(f'{cell}_ury') <= between_rows[i-1]

        for l, r in zip(row[:-1], row[1:]):
            m += m.var_by_name(f'{l}_urx') <= m.var_by_name(f'{r}_llx')





def place(*, sizes, wires, place_on_grid, fp, symmetrize=False):
    m = Model(sense=MINIMIZE, solver_name=CBC)
    m.verbose = 0


    for k, _ in sizes.items():
        for tag in ['llx', 'lly', 'urx', 'ury']:
            m.add_var(name=f'{k}_{tag}', lb=-INF)
        
        for tag in ['X', 'Y']:
            f = m.add_var(name=f'{k}_f{tag}', var_type=BINARY)

        size = dict(zip("xy", sizes[k]))

        if k in place_on_grid:
            for d in place_on_grid[k]:
                one_hots = defaultdict(list)
                axis = d['axis']
                pitch = d['pitch']
                for dd in d['ored_terms']:
                    offsets = dd['offsets']
                    scalings = dd['scalings']
                    assert set(scalings) == {-1} or set(scalings) == {1} or set(scalings) == {-1,1}
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

                f = m.var_by_name(f'{k}_f{axis.upper()}')
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

     

    floorplan(m, sizes, fp)
    wire_length(m, sizes, wires)

    m.var_by_name('llx').lb = 0
    m.var_by_name('lly').lb = 0

    z = m.add_var('z')

    m += 1*m.var_by_name('urx') + 1*m.var_by_name('ury') + 1*m.var_by_name('hpwl') == z

    m.objective += minimize(z)

    m.write('model.lp')

    status = m.optimize()
    if status == OptimizationStatus.OPTIMAL:
        print(f'optimal solution found: cost={m.objective_value}')
    elif status == OptimizationStatus.FEASIBLE:
        print(f'solution with cost {m.objective_value} current lower bound: {m.objective_bound}')
    elif status == OptimizationStatus.NO_SOLUTION_FOUND:
        print(f'no solution found, lower bound is: {m.objective_bound}')
    else:
        print(m.conflict_graph)

    if status == OptimizationStatus.OPTIMAL or status == OptimizationStatus.FEASIBLE:
        print('Solution:')
        for v in m.vars:
            print('\t', v.name, v.x)

    return m

def test_simple():

    place_on_grid = {'x': [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets': [2, 3], 'scalings': [1]}]}]}
    sizes = {'x': (1,1), 'y': (1,1), 'z': (1,1), 'a': (1,1), 'b': (1,1)}
    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (.75,.75,.75,.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b']
    ]

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

    assert m.var_by_name('hpwl').x == 0.5

def test_large():

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (.75,.75,.75,.75))])]
    fp = [['x', 'y', 'z'],
          ['a', 'b', 'c', 'd'],
          ['e', 'f', 'g', 'h'],
          ['i', 'j', 'k', 'l']
    ]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                           {'axis': 'x', 'pitch': 1, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]}]},
                          ] for row in fp for nm in row }

    m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

    assert m.var_by_name('hpwl').x == 1.5

    assert m.var_by_name('i_fY').x == 0
    assert m.var_by_name('e_fY').x == 1
    assert m.var_by_name('a_fY').x == 0
    assert m.var_by_name('x_fY').x == 1

def test_duplicate_offset():
    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (.75,.75,.75,.75))])]
    fp = [['x', 'y']]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1]},
                                                                    {'offsets':[0], 'scalings': [1]}]}
                          ] for row in fp for nm in row }

    with pytest.raises(Exception, match='assert 2 == 1') as exc_info:
        m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

def test_bad_scaling():
    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (.75,.75,.75,.75))])]
    fp = [['x', 'y']]
    sizes = { nm: (2,2) for row in fp for nm in row }

    place_on_grid = { nm: [{'axis': 'y', 'pitch': 4, 'ored_terms': [{'offsets':[0], 'scalings': [-1,1,2]}]}
                          ] for row in fp for nm in row }

    with pytest.raises(Exception, match='assert') as exc_info:
        m = place(sizes=sizes, wires=wires, fp=fp, place_on_grid=place_on_grid)

if __name__ == "__main__":
    test_two()
