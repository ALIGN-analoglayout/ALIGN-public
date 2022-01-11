
from align.schema.constraint import OffsetsScalings, PlaceOnGrid
from align.pnr.grid_constraints import lcm, check, merge, gen_constraints, split_directions_and_merge
from pytest import raises
from collections import defaultdict
import json

def test_lcm():
    with raises(AssertionError):
        lcm()

    assert lcm(2) == 2
    assert lcm(2, 3) == 6
    assert lcm(2, 3, 4) == 12
    assert lcm(2, 3, 4, 5) == 60
    assert lcm(2, 3, 4, 5, 6) == 60

def test_check():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=3, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])

    assert check(r0, 0, 1)
    assert not check(r0, 1,  1)
    assert check(r0, 2, 1)
    assert check(r1, 0, 1)
    assert not check(r1, 1,  1)
    assert check(r1, 3, 1)
    assert not check(r1, 0, -1)


def test_merge1():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0, 1, 3], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1, -1])])
    r = merge(r0, r1)
    assert r.pitch == 12
    assert r.ored_terms[0].offsets == [0, 1, 7, 8]
    assert r.ored_terms[0].scalings == [1]



def test_merge2():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0], scalings=[-1]), OffsetsScalings(offsets=[1], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1, -1])])
    r = merge(r0, r1)
    assert r.pitch == 12
    assert r.ored_terms[0].offsets == [1]
    assert r.ored_terms[0].scalings == [1]
    assert r.ored_terms[1].offsets == [0, 8]
    assert r.ored_terms[1].scalings == [-1]


def test_merge3():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1])])
    r = merge(r0, r1)
    assert r.pitch == 12
    assert r.ored_terms[0].offsets == [0, 1, 8]
    assert r.ored_terms[0].scalings == [1]


def test_merge4():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=3, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    r = merge(r0, r1)
    assert r.pitch == 6
    assert r.ored_terms[0].offsets == [0, 4]
    assert r.ored_terms[0].scalings == [1]

def test_merge5():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='V', pitch=3, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    with raises(AssertionError):
        r = merge(r0, r1)

def test_split_directions_and_merge():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='V', pitch=3, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    rs = split_directions_and_merge(r0, r1)

    by_direction = defaultdict(list)
    for r in rs:
        by_direction[r.direction].append(r)

    assert len(by_direction['H']) == 1
    assert len(by_direction['V']) == 1

    assert by_direction['H'][0].pitch == 2
    assert by_direction['V'][0].pitch == 3
    
def test_gen_constraints():

    leaf_a0 = {
        "abstract_name": "A",
        "concrete_name": "A_0",
        "bbox": [0,0,10,10],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 20,
                "ored_terms": [{"offsets": [0], "scalings": [1]}]
            }
        ]
    }

    leaf_b0 = {
        "abstract_name": "B",
        "concrete_name": "B_0",
        "bbox": [0,0,10,10],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 20,
                "ored_terms": [{"offsets": [10], "scalings": [1]}]
            }
        ]
    }

    module_top = {
        "abstract_name": "T",
        "concrete_name": "T_0",
        "bbox": [0,0,10,20],
        "constraints": [],
        "instances": [
            {
                "abstract_template_name": "A",
                "concrete_template_name": "A_0",
                "fa_map": [],
                "instance_name": "U0",
                "transformation": { 'oX': 0, 'oY': 0, 'sX': 1, 'sY': 1}
            },
            {
                "abstract_template_name": "B",
                "concrete_template_name": "B_0",
                "fa_map": [],
                "instance_name": "U1",
                "transformation": { 'oX': 0, 'oY': 10, 'sX': 1, 'sY': 1}
            }
        ]
    }

    placement_verilog_d = { "global_signals": [], "leaves": [leaf_a0, leaf_b0], "modules": [module_top]}

    gen_constraints(placement_verilog_d, 'T_0')
    print(json.dumps(module_top['constraints'], indent=2))

def test_gen_constraints_multiple():

    leaf_a0 = {
        "abstract_name": "A",
        "concrete_name": "A_0",
        "bbox": [0,0,1,1],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 4,
                "ored_terms": [{"offsets": [0, 1], "scalings": [1]}]
            }
        ]
    }

    leaf_b0 = {
        "abstract_name": "B",
        "concrete_name": "B_0",
        "bbox": [0,0,1,1],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 6,
                "ored_terms": [{"offsets": [0, 1, 2], "scalings": [1]}]
            }
        ]
    }

    module_top = {
        "abstract_name": "T",
        "concrete_name": "T_0",
        "bbox": [0,0,1,6],
        "constraints": [],
        "instances": [
            {
                "abstract_template_name": "A",
                "concrete_template_name": "A_0",
                "fa_map": [],
                "instance_name": "U0",
                "transformation": { 'oX': 0, 'oY': 5, 'sX': 1, 'sY': 1}
            },
            {
                "abstract_template_name": "B",
                "concrete_template_name": "B_0",
                "fa_map": [],
                "instance_name": "U1",
                "transformation": { 'oX': 0, 'oY': 2, 'sX': 1, 'sY': 1}
            }
        ]
    }

    placement_verilog_d = { "global_signals": [], "leaves": [leaf_a0, leaf_b0], "modules": [module_top]}

    gen_constraints(placement_verilog_d, 'T_0')
    print(json.dumps(module_top['constraints'], indent=2))

    assert module_top['constraints'][0]['pitch'] == 12
    assert module_top['constraints'][0]['ored_terms'][0]['offsets'] == [0, 4, 11]

def test_gen_constraints_internal():

    leaf_a0 = {
        "abstract_name": "A",
        "concrete_name": "A_0",
        "bbox": [0,0,1,1],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 4,
                "ored_terms": [{"offsets": [0, 1], "scalings": [1]}]
            }
        ]
    }

    leaf_b0 = {
        "abstract_name": "B",
        "concrete_name": "B_0",
        "bbox": [0,0,1,1],
        "terminals": [],
        "constraints": [
            {
                "constraint": "place_on_grid",
                "direction": "V",
                "pitch": 6,
                "ored_terms": [{"offsets": [0, 1, 2], "scalings": [1]}]
            }
        ]
    }

    module_internal = {
        "abstract_name": "C",
        "concrete_name": "C_0",
        "bbox": [0,0,1,6],
        "constraints": [],
        "instances": [
            {
                "abstract_template_name": "A",
                "concrete_template_name": "A_0",
                "fa_map": [],
                "instance_name": "U0",
                "transformation": { 'oX': 0, 'oY': 5, 'sX': 1, 'sY': 1}
            },
            {
                "abstract_template_name": "B",
                "concrete_template_name": "B_0",
                "fa_map": [],
                "instance_name": "U1",
                "transformation": { 'oX': 0, 'oY': 2, 'sX': 1, 'sY': 1}
            }
        ]
    }

    module_top = {
        "abstract_name": "T",
        "concrete_name": "T_0",
        "bbox": [0,0,3,17],
        "constraints": [],
        "instances": [
            {
                "abstract_template_name": "C",
                "concrete_template_name": "C_0",
                "fa_map": [],
                "instance_name": "U0",
                "transformation": { 'oX': 0, 'oY': 0, 'sX': 1, 'sY': 1}
            },
            {
                "abstract_template_name": "C",
                "concrete_template_name": "C_0",
                "fa_map": [],
                "instance_name": "U1",
                "transformation": { 'oX': 1, 'oY': 4, 'sX': 1, 'sY': 1}
            },
            {
                "abstract_template_name": "C",
                "concrete_template_name": "C_0",
                "fa_map": [],
                "instance_name": "U2",
                "transformation": { 'oX': 2, 'oY': 11, 'sX': 1, 'sY': 1}
            },
        ]
    }

    placement_verilog_d = { "global_signals": [], "leaves": [leaf_a0, leaf_b0], "modules": [module_top,module_internal]}

    gen_constraints(placement_verilog_d, 'T_0')
    print(json.dumps(module_top['constraints'], indent=2))

    print(module_internal['constraints'])
    print(module_top['constraints'])

    assert module_internal['constraints'][0]['pitch'] == 12
    assert module_internal['constraints'][0]['ored_terms'][0]['offsets'] == [0, 4, 11]

    assert module_top['constraints'][0]['pitch'] == 12
    assert module_top['constraints'][0]['ored_terms'][0]['offsets'] == [0]

    module_top['instances'][2]['transformation']['oY'] = 10
    module_internal['constraints'] = []
    module_top['constraints'] = []

    with raises(AssertionError):
        gen_constraints(placement_verilog_d, 'T_0')

