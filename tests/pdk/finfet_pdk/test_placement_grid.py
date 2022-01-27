import os
import json
import pytest
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits
from align.pdk.finfet import MOSGenerator


def test_place_on_grid():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=True, n=8)


def test_scalings():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    mp0 o a vccx vccx p w=45e-9 m=1 nf=1
    mn0 o a vssx vssx n w=45e-9 m=1 nf=1
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    xi2 v2 vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "AlignInOrder", "line": "left", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=8)

    # Check if the PlaceOnGrid constraint is written to primitive.json
    filename = run_dir / '3_pnr' / 'inputs' / 'DIG22INV.json'
    assert filename.exists() and filename.is_file()
    with (filename).open('rt') as fp:
        primitive = json.load(fp)
        assert 'metadata' in primitive
        assert 'constraints' in primitive['metadata']

        golden = [{
            "constraint": "place_on_grid",
            "direction": "H",
            "pitch": 12600,
            "ored_terms": [{"offsets": [0], "scalings": [1, -1]}]
        }]
        assert primitive['metadata']['constraints'] == golden


def test_hierarchy():
    os.environ['PLACE_ON_GRID'] = 't'
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": False},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)


@pytest.mark.parametrize('vt', ['NMOS', 'PMOS'])
def test_check_constraints(vt):
    os.environ['PLACE_ON_GRID'] = 't'
    c = MOSGenerator()
    ports = {'S': [('M1', 'S')], 'D': [('M1', 'D')], 'G': [('M1', 'G')]}
    parameters = {'M': 1, 'NFIN': 4, 'real_inst_type': vt, 'NF': 2}
    c.addNMOSArray(1, 1, 0, None, ports, **parameters)
    assert c.metadata["constraints"][0]["constraint"] == "place_on_grid"
