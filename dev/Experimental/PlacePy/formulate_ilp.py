import mip
import itertools
import numpy as np
import time
import plotly.graph_objects as go
import plotly.express as px


def measure_time(func):
    def wrapper(*args, **kwargs):
        s = time.time()
        returned_value = func(*args, **kwargs)
        e = time.time() - s
        print(f"Elapsed time: {e:.3f} secs")
        return returned_value
    return wrapper


@measure_time
def formulate_problem(constraints, instance_map, instance_sizes, sequence_pair, size_mode=0):

    model = mip.Model(sense=mip.MINIMIZE, solver_name=mip.CBC)
    model.verbose = 0  # set to one to see more progress output with the solver

    upper_bound = 1e9  # 100mm=100e6nm=1e9 angstrom
    model.add_var(name='W', lb=0, ub=upper_bound)
    model.add_var(name='H', lb=0, ub=upper_bound)

    for name, _ in instance_map.items():
        for tag in ['llx', 'lly', 'urx', 'ury']:
            model.add_var(name=f'{name}_{tag}', lb=0, ub=upper_bound)

        model += model.var_by_name(f'{name}_urx') <= model.var_by_name("W")
        model += model.var_by_name(f'{name}_ury') <= model.var_by_name("H")

        if size_mode == 0:  # Hard block (width, height)
            model += model.var_by_name(f'{name}_urx') - model.var_by_name(f'{name}_llx') == instance_sizes[name][0]
            model += model.var_by_name(f'{name}_ury') - model.var_by_name(f'{name}_lly') == instance_sizes[name][1]
        else:  # Soft block (area, aspect_ratio_min, aspect_ratio_max)
            assert False, "Not implemented yet"

    reverse_map = {v: k for k, v in instance_map.items()}
    instance_pos = {reverse_map[index]: i for i, index in enumerate(sequence_pair[0])}
    instance_neg = {reverse_map[index]: i for i, index in enumerate(sequence_pair[1])}

    for index0, index1 in itertools.combinations(reverse_map, 2):
        name0 = reverse_map[index0]
        name1 = reverse_map[index1]
        assert name0 != name1
        if instance_pos[name0] < instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:    # bb
            model += model.var_by_name(f'{name0}_urx') <= model.var_by_name(f'{name1}_llx')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # aa
            model += model.var_by_name(f'{name1}_urx') <= model.var_by_name(f'{name0}_llx')
        elif instance_pos[name0] < instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # ba
            model += model.var_by_name(f'{name1}_ury') <= model.var_by_name(f'{name0}_lly')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:  # ab
            model += model.var_by_name(f'{name0}_ury') <= model.var_by_name(f'{name1}_lly')
        else:
            assert False

    model.objective += model.var_by_name("W") + model.var_by_name("H")

    model.write("model.lp")

    status = model.optimize(max_seconds_same_incumbent=60.0)
    if status == mip.OptimizationStatus.OPTIMAL:
        print(f'optimal solution found: cost={model.objective_value}')
    elif status == mip.OptimizationStatus.FEASIBLE:
        print(f'solution with cost {model.objective_value} current lower bound: {model.objective_bound}')
    else:
        raise Exception('No solution to ILP')
    if status == mip.OptimizationStatus.OPTIMAL or status == mip.OptimizationStatus.FEASIBLE:
        if model.verbose:
            print('Solution:')
            for v in model.vars:
                print('\t', v.name, v.x)
            print(f'Number of solutions: {model.num_solutions}')

    return model


# Tests
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context


def draw(model, instance_map, wires):

    colorscale = px.colors.qualitative.Alphabet

    fig = go.Figure()
    fig.update_xaxes(range=[0, model.var_by_name('W').x+1])
    fig.update_yaxes(range=[0, model.var_by_name('H').x+1])

    # Add shapes
    x_lst = list()
    y_lst = list()
    n_lst = list()
    for name, i in instance_map.items():
        llx, lly = model.var_by_name(f'{name}_llx').x, model.var_by_name(f'{name}_lly').x
        urx, ury = model.var_by_name(f'{name}_urx').x, model.var_by_name(f'{name}_ury').x
        assert urx > llx and ury > lly
        color = colorscale[i % len(colorscale)]
        fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="RoyalBlue", width=3), fillcolor=color)
        x_lst.append((llx+urx)/2)
        y_lst.append((lly+ury)/2)
        n_lst.append(f"${name}$")

    fig.update_shapes(opacity=0.5, xref="x", yref="y")

    # Add labels
    fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=n_lst, mode="text", textfont=dict(color="black", size=196)))

    fig.show()


def initialize_constraints(n):
    library = Library()
    with set_context(library):
        model = Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={})
        library.append(model)
        subckt = SubCircuit(name='SUBCKT', pins=['PIN1', 'PIN2'], parameters={})
        library.append(subckt)
    with set_context(subckt.elements):
        for i in range(n):
            subckt.elements.append(Instance(name=f'M{i}', model='TwoTerminalDevice', pins={'A': 'PIN1', 'B': 'PIN2'}))
    instance_map = {f'M{i}': i for i in range(n)}
    return subckt.constraints, instance_map


def test_formulate_problem():
    constraints, instance_map = initialize_constraints(2)
    instance_sizes = {"M0": (10, 5), "M1": (4, 2)}
    sequence_pair = ((0, 1), (0, 1))
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair)

    n = 15
    constraints, instance_map = initialize_constraints(n)
    instance_sizes = {f"M{k}": (k+1, k+1) for k in range(n)}
    sequence_pair = (list(np.random.permutation(n)), list(np.random.permutation(n)))
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair)
    draw(model, instance_map, [])


test_formulate_problem()
