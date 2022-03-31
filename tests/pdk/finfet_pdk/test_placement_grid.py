import os
import json
import shutil
import pytest
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits
from align.schema.constraint import OffsetsScalings, PlaceOnGrid
import align

"""
monkeypatch.setattr on MOSGenerator does not work probably due to reloading the module in get_generator
"""


@pytest.fixture
def placer_max_iter(monkeypatch):
    # Reduce number of iterations to speed up tests
    monkeypatch.setattr(align.pnr.placer, "PLACER_SA_MAX_ITER", 10)


@pytest.fixture
def place_on_grid_h(monkeypatch):
    rh = 6300
    ored_terms = [
        OffsetsScalings(offsets=[0*rh], scalings=[1, -1]),
        OffsetsScalings(offsets=[2*rh], scalings=[1, -1])
    ]
    place_on_grid = {'constraints': [
        PlaceOnGrid(direction='H', pitch=4*rh, ored_terms=ored_terms).dict()
    ]}
    monkeypatch.setenv('PLACE_ON_GRID', json.dumps(place_on_grid))


@pytest.fixture
def place_on_grid_v(monkeypatch):
    pp = 1080
    ored_terms = [
        OffsetsScalings(offsets=[pp], scalings=[1, -1]),
    ]
    place_on_grid = {'constraints': [
        PlaceOnGrid(direction='V', pitch=2*pp, ored_terms=ored_terms).dict()
    ]}
    monkeypatch.setenv('PLACE_ON_GRID', json.dumps(place_on_grid))


def test_scalings(place_on_grid_h):
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
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "AlignInOrder", "line": "left", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=8)

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
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_check_metadata(place_on_grid_h):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False,  additional_args=['--flow_stop', '2_primitives'])
    prim_dir = run_dir/'2_primitives'
    for filename in prim_dir.glob('*.json'):
        if str(filename).endswith('.gds.json') or str(filename.stem).startswith('__primitives'):
            continue
        with (filename).open('rt') as fp:
            primitive = json.load(fp)
            assert primitive['metadata']['constraints'][0]['constraint'] == 'place_on_grid', filename.stem
            assert primitive['metadata']['constraints'][0]['direction'] == 'H', filename.stem
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ota_on_grid_h(place_on_grid_h):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)


def test_ota_on_grid_v(place_on_grid_v):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)


def cmp_constraints(name):
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn", "invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["ccp"], ["ccn"], ["dp"], ["mn0"], ["invn", "invp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    return constraints


def test_cmp_on_grid(place_on_grid_h, placer_max_iter):
    print(f'PLACE_ON_GRID={os.environ["PLACE_ON_GRID"]}')
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = cmp_constraints(name)
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)
