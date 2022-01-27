import os
import json
import shutil
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits


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


def test_check_constraints():
    os.environ['PLACE_ON_GRID'] = 't'
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vi vo vbp vccx vssx
        mp0 vo vbp vccx vccx p w=720e-9 nf=4 m=4
        mn0 vo vi vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=1, cleanup=False, additional_args=['--flow_stop', '2_primitives'])
    name = name.upper()
    primitives_folder = run_dir / '2_primitives'
    for dev in ['NMOS', 'PMOS']:
        mos = [f for f in primitives_folder.glob(f'{dev}*[0-9].json')][0]
        with (mos).open('rt') as fp:
            data = json.load(fp)
            assert "metadata" in data
            assert "constraints" in data["metadata"]
            assert data["metadata"]["constraints"][0]["constraint"] == "place_on_grid"
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
