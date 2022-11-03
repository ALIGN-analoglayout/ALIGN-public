import mip
import itertools
import numpy as np
import time
import plotly.graph_objects as go
import plotly.express as px
from collections import defaultdict
# imports for testing
import pytest
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context
import align.schema.constraint as constraint_schema


def measure_time(func):
    def wrapper(*args, **kwargs):
        s = time.time()
        returned_value = func(*args, **kwargs)
        e = time.time() - s
        print(f"Elapsed time: {e:.3f} secs")
        return returned_value
    return wrapper


@measure_time
def formulate_problem(constraints, instance_map, instance_sizes, sequence_pair, place_on_grid=None, size_mode=0):

    model = mip.Model(sense=mip.MINIMIZE, solver_name=mip.CBC)
    model.verbose = 0  # set to one to see more progress output with the solver

    upper_bound = 1e9  # 100mm=100e6nm=1e9 angstrom
    model.add_var(name='W', lb=0, ub=upper_bound)
    model.add_var(name='H', lb=0, ub=upper_bound)

    for name, _ in instance_map.items():

        size = dict(zip("xy", instance_sizes[name]))

        # Define instance variables
        for tag in ['llx', 'lly', 'urx', 'ury']:
            model.add_var(name=f'{name}_{tag}', lb=0, ub=upper_bound)
        for tag in ['fx', 'fy']:
            model.add_var(name=f'{name}_{tag}', var_type=mip.BINARY)

        # Instance width and height
        model += model.var_by_name(f'{name}_urx') - model.var_by_name(f'{name}_llx') == size['x']
        model += model.var_by_name(f'{name}_ury') - model.var_by_name(f'{name}_lly') == size['y']

        # All instances within the bounding box
        model += model.var_by_name(f'{name}_urx') <= model.var_by_name("W")
        model += model.var_by_name(f'{name}_ury') <= model.var_by_name("H")

        # PlaceOnGrid constraints
        if place_on_grid and name in place_on_grid:
            assert len(place_on_grid[name]) <= 2
            for constraint in place_on_grid[name]:
                axis = 'x' if constraint['direction'] == 'H' else 'y'
                pitch = constraint['pitch']
                flip = model.var_by_name(f'{name}_f{axis}')

                offset_scalings = defaultdict(list)
                offset_variables = list()
                for term in constraint['ored_terms']:
                    offsets = term['offsets']
                    scalings = term['scalings']
                    assert set(scalings) in [{1}, {-1}, {-1, 1}]
                    for offset in offsets:
                        offset_scalings[offset].extend(scalings)
                for offset, scalings in offset_scalings.items():
                    var = model.add_var(var_type=mip.BINARY)
                    offset_variables.append((offset, var))
                    if set(scalings) == {1}:
                        model += var + flip <= 1
                    elif set(scalings) == {-1}:
                        model += var <= flip
                model += mip.xsum(var[1] for var in offset_variables) == 1
                grid = model.add_var(name=f'{name}_grid_{axis}', var_type=mip.INTEGER, lb=0)
                origin = grid*pitch + mip.xsum(v[0]*v[1] for v in offset_variables)
                model += origin - size[axis] * flip == model.var_by_name(f'{name}_ll{axis}')

    # Constraints implied by the sequence pairs
    reverse_map = {v: k for k, v in instance_map.items()}
    instance_pos = {reverse_map[index]: i for i, index in enumerate(sequence_pair[0])}
    instance_neg = {reverse_map[index]: i for i, index in enumerate(sequence_pair[1])}
    for index0, index1 in itertools.combinations(reverse_map, 2):
        name0 = reverse_map[index0]
        name1 = reverse_map[index1]
        assert name0 != name1
        if instance_pos[name0] < instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:    # bb = LEFT
            model += model.var_by_name(f'{name0}_urx') <= model.var_by_name(f'{name1}_llx')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # aa = RIGHT
            model += model.var_by_name(f'{name1}_urx') <= model.var_by_name(f'{name0}_llx')
        elif instance_pos[name0] < instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # ba = ABOVE
            model += model.var_by_name(f'{name1}_ury') <= model.var_by_name(f'{name0}_lly')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:  # ab = BELOW
            model += model.var_by_name(f'{name0}_ury') <= model.var_by_name(f'{name1}_lly')
        else:
            assert False

    # Placement constraints
    for constraint in constraints:

        if isinstance(constraint, constraint_schema.Boundary):
            if max_width := getattr(constraint, "max_width", False):
                model += model.var_by_name('W') <= max_width
            if max_height := getattr(constraint, "max_height", False):
                model += model.var_by_name('H') <= max_height

        if isinstance(constraint, constraint_schema.PlaceOnBoundary):
            for name in constraint.instances_on(["north", "northwest", "northeast"]):
                model += model.var_by_name(f'{name}_ury') == model.var_by_name('H')
            for name in constraint.instances_on(["south", "southwest", "southeast"]):
                model += model.var_by_name(f'{name}_lly') == 0
            for name in constraint.instances_on(["east", "northeast", "southeast"]):
                model += model.var_by_name(f'{name}_urx') == model.var_by_name('W')
            for name in constraint.instances_on(["west", "northwest", "southwest"]):
                model += model.var_by_name(f'{name}_llx') == 0

    # Minimize the perimeter of the bounding box
    model.objective += model.var_by_name("W") + model.var_by_name("H")

    model.write("model.lp")

    # Solve
    status = model.optimize(max_seconds_same_incumbent=60.0, max_seconds=300)
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


DRAW = False


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


def test_basic_1():
    n = 2
    constraints, instance_map = initialize_constraints(n)
    instance_sizes = {"M0": (9, 5), "M1": (4, 2)}
    sequence_pair = ((0, 1), (0, 1))
    c = [
        {"constraint": "place_on_grid", "direction": "H", "pitch": 10, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]},
        {"constraint": "place_on_grid", "direction": "V", "pitch": 2, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]}
        ]
    place_on_grid = {f"M{i}": c for i in range(n)}
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair, place_on_grid=place_on_grid)
    if DRAW:
        draw(model, instance_map, [])


@pytest.mark.parametrize("iter", [i for i in range(10)])
def test_basic_2(iter):
    n = 10
    constraints, instance_map = initialize_constraints(n)
    instance_sizes = {f"M{k}": (1+(1*k)//2, 10) for k in range(n)}
    sequence_pair = (list(np.random.permutation(n)), list(np.random.permutation(n)))
    c = [
        {"constraint": "place_on_grid", "direction": "H", "pitch": 10, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]},
        {"constraint": "place_on_grid", "direction": "V", "pitch": 2, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]}
        ]
    place_on_grid = {f"M{i}": c for i in range(n)}
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair, place_on_grid=place_on_grid)
    if DRAW:
        draw(model, instance_map, [])


def test_boundary():
    n = 5
    constraints, instance_map = initialize_constraints(n)
    with set_context(constraints):
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=8))
    instance_sizes = {f"M{k}": (2, 2) for k in range(n)}
    sequence_pair = ([k for k in range(n)], [k for k in range(n)])
    with pytest.raises(Exception) as _:
        formulate_problem(constraints, instance_map, instance_sizes, sequence_pair)

    with set_context(constraints):
        constraints.pop()
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=10))
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair)
    if DRAW:
        draw(model, instance_map, [])
    for v in model.vars:
        if v.name == 'H':
            break
    assert v.x <= 10


def test_place_on_boundary():
    n = 4
    constraints, instance_map = initialize_constraints(n)
    with set_context(constraints):
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=10))
        constraints.append(constraint_schema.PlaceOnBoundary(northwest="M0", northeast="M1", southwest="M2", southeast="M3"))
    instance_sizes = {f"M{k}": (1+k, 1+k) for k in range(n)}
    sequence_pair = ([0, 1, 2, 3], [2, 3, 0, 1])
    model = formulate_problem(constraints, instance_map, instance_sizes, sequence_pair)
    if DRAW:
        draw(model, instance_map, [])
