import itertools
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
import pytest

import align.schema.constraint as constraint_schema
from align.schema.types import set_context
from align.schema import Model, Instance, SubCircuit, Library
from align.pnr.placer_pythonic_sp import enumerate_sequence_pairs, enumerate_block_variants, place_sequence_pair

DRAW = False


def draw(model, instance_map, instance_sizes=None, wires=None):
    if not DRAW:
        return

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
        n_lst.append(f"{name}")

    if instance_sizes and wires:
        i = 0
        for name, instance_bbox in wires.items():
            color = colorscale[i % len(colorscale)]
            for instance, bbox in instance_bbox:
                size = dict(zip("xy", instance_sizes[instance]))
                bb = dict()
                for (tag, axis), offset in zip(itertools.product(['ll', 'ur'], ['x', 'y']), bbox):
                    bb[tag+axis] = model.var_by_name(f'{instance}_ll{axis}').x + offset + \
                                (size[axis] - 2*offset) * model.var_by_name(f'{instance}_f{axis}').x
                llx, urx = min(bb['llx'], bb['urx']), max(bb['llx'], bb['urx'])
                lly, ury = min(bb['lly'], bb['ury']), max(bb['lly'], bb['ury'])
                fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="Black", width=1), fillcolor=color)
                x_lst.append((llx+urx)/2)
                y_lst.append((lly+ury)/2)
                n_lst.append(f"{name}")
            i += 1

    fig.update_shapes(opacity=0.5, xref="x", yref="y")

    # Add labels
    fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=n_lst, mode="text", textfont=dict(color="black", size=24)))

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


def test_enumerate_sequence_pairs():

    constraints, instance_map = initialize_constraints(2)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 100)
    assert len(sequence_pairs) == 4

    constraints, instance_map = initialize_constraints(4)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 576

    constraints, instance_map = initialize_constraints(20)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1000

    constraints, instance_map = initialize_constraints(4)
    with set_context(constraints):
        constraints.append(constraint_schema.Order(direction='left_to_right', instances=[f'M{i}' for i in range(4)]))
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1
    assert sequence_pairs[0] == ((0, 1, 2, 3), (0, 1, 2, 3))

    constraints, instance_map = initialize_constraints(4)
    with set_context(constraints):
        constraints.append(constraint_schema.Order(direction='top_to_bottom', instances=[f'M{i}' for i in range(4)]))
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1
    assert sequence_pairs[0] == ((0, 1, 2, 3), (3, 2, 1, 0))


def test_enumerate_block_variants():

    constraints, instance_map = initialize_constraints(2)
    variant_counts = {"M0": 4, "M1": 5}
    variants = enumerate_block_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 20

    constraints, instance_map = initialize_constraints(4)
    variant_counts = {k: 2 for k in instance_map.keys()}
    with set_context(constraints):
        constraints.append(constraint_schema.SameTemplate(instances=[f'M{i}' for i in range(4)]))
    variants = enumerate_block_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 2
    assert variants == [tuple([0]*4), tuple([1]*4)]

    constraints, instance_map = initialize_constraints(4)
    variant_counts = {k: 3 for k in instance_map.keys()}
    with set_context(constraints):
        constraints.append(constraint_schema.SameTemplate(instances=["M1", "M2"]))
        constraints.append(constraint_schema.SameTemplate(instances=["M2", "M3"]))
    variants = enumerate_block_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 3*3


def test_place_sequence_pair_1():
    n = 2
    constraints, instance_map = initialize_constraints(n)
    instance_sizes = {"M0": (9, 5), "M1": (4, 2)}
    sequence_pair = ((0, 1), (0, 1))
    c = [
        {"constraint": "place_on_grid", "direction": "H", "pitch": 2, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]},
        {"constraint": "place_on_grid", "direction": "V", "pitch": 2, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]}
        ]
    wires = {
        'net1': [('M0', (1, 2, 2, 2.25)), ('M1', (3, 1, 4, 1.25))]
        }
    place_on_grid = {f"M{i}": c for i in range(n)}
    solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=wires, place_on_grid=place_on_grid)
    assert solution['transformations']['M0'] == {'oX': 10, 'oY': 0, 'sX': -1, 'sY': 1}
    assert solution['transformations']['M1'] == {'oX': 14, 'oY': 4, 'sX': -1, 'sY': -1}
    draw(solution['model'], instance_map, instance_sizes, wires)


@pytest.mark.parametrize("iter", [i for i in range(10)])
def test_place_sequence_pair_2(iter):
    n = 10
    constraints, instance_map = initialize_constraints(n)
    instance_sizes = {f"M{k}": (1+(1*k)//2, 10) for k in range(n)}
    sequence_pair = (list(np.random.permutation(n)), list(np.random.permutation(n)))
    c = [
        {"constraint": "place_on_grid", "direction": "H", "pitch": 10, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]},
        {"constraint": "place_on_grid", "direction": "V", "pitch": 2, "ored_terms": [{'offsets': [0], 'scalings': [-1, 1]}]}
        ]
    place_on_grid = {f"M{i}": c for i in range(n)}
    solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, place_on_grid=place_on_grid)
    draw(solution['model'], instance_map)


def test_place_sequence_pair_boundary():
    n = 5
    constraints, instance_map = initialize_constraints(n)
    with set_context(constraints):
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=8))
    instance_sizes = {f"M{k}": (2, 2) for k in range(n)}
    sequence_pair = ([k for k in range(n)], [k for k in range(n)])
    assert not place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair)

    with set_context(constraints):
        constraints.pop()
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=10))
    solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair)
    draw(solution['model'], instance_map)
    for v in solution['model'].vars:
        if v.name == 'H':
            break
    assert v.x <= 10


def test_place_sequence_pair_place_on_boundary():
    n = 4
    constraints, instance_map = initialize_constraints(n)
    with set_context(constraints):
        constraints.append(constraint_schema.Boundary(subcircuit="subckt", max_height=10, max_width=10))
        constraints.append(constraint_schema.PlaceOnBoundary(northwest="M0", northeast="M1", southwest="M2", southeast="M3"))
    instance_sizes = {f"M{k}": (1+k, 1+k) for k in range(n)}
    sequence_pair = ([0, 1, 2, 3], [2, 3, 0, 1])
    solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair)
    draw(solution['model'], instance_map)
