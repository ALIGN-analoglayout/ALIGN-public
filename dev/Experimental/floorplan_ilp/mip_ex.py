
from mip import *

def wire_length(m):

    ...




def floorplan(m):
    sizes = {'x': (1,1), 'y': (1,1), 'z': (1,1), 'a': (1,1), 'b': (1,1)}

    for k, _ in sizes.items():
        for tag in ['llx', 'lly', 'urx', 'ury']:
            m.add_var(name=f'{k}_{tag}')

    for tag in ['llx', 'lly', 'urx', 'ury']:
        m.add_var(name=f'{tag}')   

    for k, v in sizes.items():
        m += m.var_by_name(f'{k}_llx') + v[0] == m.var_by_name(f'{k}_urx')
        m += m.var_by_name(f'{k}_lly') + v[1] == m.var_by_name(f'{k}_ury')

    fp = [['x', 'y', 'z'],
          ['a', 'b']
    ]

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

    floorplan(m)

    m.var_by_name('llx').lb = 0
    m.var_by_name('lly').lb = 0

    z = m.add_var('z')

    m += m.var_by_name('urx') + m.var_by_name('ury') <= z

    m.objective += minimize(z)

    m.write('model.lp')

    status = m.optimize()
    if status == OptimizationStatus.OPTIMAL:
        print(f'optimal solution found: cost={m.objective_value}')
    elif status == OptimizationStatus.FEASIBLE:
        print(f'solution with cost {m.objective_value} current lower bound: {m.objective_bound}')
    elif status == OptimizationStatus.NO_SOLUTION_FOUND:
        print(f'no solution found, lower bound is: {m.objective_bound}')

    if status == OptimizationStatus.OPTIMAL or status == OptimizationStatus.FEASIBLE:
        print(f'solution: {[v.x for v in m.vars]}')


if __name__ == "__main__":
    main()