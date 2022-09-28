
from mip import *
from itertools import product

def wire_length(m, sizes, wires):
    for wire_name, terminals in wires:

        for tag, axis in product(['ll', 'ur'], ['x', 'y']):
            m.add_var(name=f'{wire_name}_{tag}{axis}')

        for instance, bbox in terminals:
            size = dict(zip("xy", sizes[instance]))
            for (tag, axis), offset in zip(product(['ll', 'ur'], ['x', 'y']), bbox):
                Q = size[axis] / 2
                P = offset - Q
                eqn = P * m.var_by_name(f'{instance}_s{axis.upper()}') + Q + m.var_by_name(f'{instance}_ll{axis}')
                m += eqn <= m.var_by_name(f'{wire_name}_ur{axis}')
                m += m.var_by_name(f'{wire_name}_ll{axis}') <= eqn

    hpwl = m.add_var(name='hpwl')

    m += xsum(m.var_by_name(f'{wire_name}_ur{axis}') for wire_name, _ in wires for axis in ['x', 'y']) - \
        xsum(m.var_by_name(f'{wire_name}_ll{axis}') for wire_name, _ in wires for axis in ['x', 'y']) == hpwl



    ...




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





def main():
    m = Model(sense=MINIMIZE, solver_name=CBC)

    sizes = {'x': (1,1), 'y': (1,1), 'z': (1,1), 'a': (1,1), 'b': (1,1)}

    wires = [('w', [('x', (.25,.25,.25,.25)), ('y', (.75,.75,.75,.75))])]

    fp = [['x', 'y', 'z'],
          ['a', 'b']
    ]

    for k, _ in sizes.items():
        for tag in ['llx', 'lly', 'urx', 'ury']:
            m.add_var(name=f'{k}_{tag}')
        
        for tag in ['X', 'Y']:
            f = m.add_var(name=f'{k}_f{tag}', var_type=BINARY)
            s = m.add_var(name=f'{k}_s{tag}', lb=-INF)

            m += 1 - 2*f == s

    for tag in ['llx', 'lly', 'urx', 'ury']:
        m.add_var(name=f'{tag}')  

     

    floorplan(m, sizes, fp)
    wire_length(m, sizes, wires)

    m.var_by_name('llx').lb = 0
    m.var_by_name('lly').lb = 0

    z = m.add_var('z')

    #m += m.var_by_name('x_fX') == 1
    #m += m.var_by_name('y_fY') == 1
    #m += m.var_by_name('y_fX') == 1

    m += m.var_by_name('urx') + m.var_by_name('ury') + m.var_by_name('hpwl') == z

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



if __name__ == "__main__":
    main()