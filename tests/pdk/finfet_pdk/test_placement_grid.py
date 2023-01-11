import os
import json
import shutil
import pytest
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits
from align.schema.constraint import OffsetsScalings, PlaceOnGrid

"""
monkeypatch.setattr on MOSGenerator does not work probably due to reloading the module in get_generator
"""

CLEANUP = False if os.getenv("CLEANUP", None) else True
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


@pytest.fixture
def place_on_grid_h(monkeypatch):
    rh = 6300
    ored_terms = [
        OffsetsScalings(offsets=[0*rh], scalings=[1, -1]),
        OffsetsScalings(offsets=[2*rh], scalings=[1, -1])
    ]
    place_on_grid = {'constraints': [PlaceOnGrid(direction='H', pitch=4*rh, ored_terms=ored_terms).dict()]}
    PLACE_ON_GRID = json.dumps(place_on_grid)
    monkeypatch.setenv('PLACE_ON_GRID', PLACE_ON_GRID)
    print(f"\n{PLACE_ON_GRID=}")


@pytest.fixture
def place_on_grid_v(monkeypatch):
    pp = 1080
    ored_terms = [OffsetsScalings(offsets=[0], scalings=[1, -1])]
    place_on_grid = {'constraints': [PlaceOnGrid(direction='V', pitch=2*pp, ored_terms=ored_terms).dict()]}
    PLACE_ON_GRID = json.dumps(place_on_grid)
    monkeypatch.setenv('PLACE_ON_GRID', PLACE_ON_GRID)
    print(f"\n{PLACE_ON_GRID=}")


@pytest.fixture
def place_on_grid_v_half(monkeypatch):
    pp = 1080
    ored_terms = [OffsetsScalings(offsets=[pp//2], scalings=[1, -1])]
    place_on_grid = {'constraints': [PlaceOnGrid(direction='V', pitch=pp, ored_terms=ored_terms).dict()]}
    PLACE_ON_GRID = json.dumps(place_on_grid)
    monkeypatch.setenv('PLACE_ON_GRID', PLACE_ON_GRID)
    print(f"\n{PLACE_ON_GRID=}")


@pytest.fixture
def disable_tap(monkeypatch):
    monkeypatch.setenv('ALIGN_DISABLE_TAP', "true")
    print(f"DISABLED TAP INSERTION")


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
        golden = [
            {
                "constraint": "PlaceOnGrid",
                "direction": "H",
                "pitch": 12600,
                "ored_terms": [{"offsets": [0], "scalings": [1, -1]}]
            },
            {
                "constraint": "PlaceOnGrid",
                "direction": "V",
                "pitch": 1080,
                "ored_terms": [{"offsets": [540], "scalings": [1, -1]}]
            }
        ]
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
            assert primitive['metadata']['constraints'][0]['constraint'] == 'PlaceOnGrid', filename.stem
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
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xg1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xg2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xg3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xg3", "xg2", "xg1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP)


def test_ota_on_grid_v(place_on_grid_v):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xg1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xg2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xg3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xg3", "xg2", "xg1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP)


def cmp_constraints(name):
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "instance_name": "xinvp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "instance_name": "xinvn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["xinvn", "xinvp"]},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["xccp"], ["xccn"], ["xdp"], ["mn0"], ["xinvn", "xinvp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "xccp", "xccn", "xdp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "ratio_low": 0.5, "ratio_high": 2}
    ]
    return constraints


def test_cmp_on_grid(place_on_grid_h):
    print(f'PLACE_ON_GRID={os.environ["PLACE_ON_GRID"]}')
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = cmp_constraints(name)
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, additional_args=["--placer_sa_iterations", "10"])


def test_cmp_on_grid_ilp(place_on_grid_h):
    print(f'PLACE_ON_GRID={os.environ["PLACE_ON_GRID"]}')
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = cmp_constraints(name)
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, additional_args=['--place_using_ILP', "--placer_sa_iterations", "10"])


def test_cs_on_grid_v(place_on_grid_v_half):
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vbs vccx vssx
        mp0 vop vbs vccx vccx p w=180e-9 nf=4 m=1
        mn0 vop vin vssx vssx n w=180e-9 nf=4 m=1
        .ends {name}
        """)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP)


def test_one_to_four():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi vo vccx vssx dig22inv
    xi1 vi vo vccx vssx dig22inv
    xi2 vi vo vccx vssx dig22inv
    xi3 vi vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {
            "constraint": "ConfigureCompiler",
            "auto_constraint": False,
            "propagate": True,
            "fix_source_drain": False,
            "merge_series_devices": False,
            "merge_parallel_devices": False,
            "remove_dummy_devices": True,
            "remove_dummy_hierarchies": False
        },
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vssx", "vccx"]},
        {"constraint": "Boundary", "halo_vertical": 0.3, "halo_horizontal": 0.216}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False, n=1)


@pytest.mark.skip(reason="This test is too slow. For a future PR.")
def test_one_to_four_missing_power():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vcc vssx
    .ends
    .subckt {name} vi vo vcccx vssx
    xi0 vi vo vcccx vssx dig22inv
    xi1 vi vo vcccx vssx dig22inv
    xi2 vi vo vcccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {
            "constraint": "ConfigureCompiler",
            "auto_constraint": False,
            "propagate": True,
            "fix_source_drain": False,
            "merge_series_devices": False,
            "merge_parallel_devices": False,
            "remove_dummy_devices": True,
            "remove_dummy_hierarchies": False
        },
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vssx", "vccx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level="INFO", n=1)


#@pytest.mark.skip(reason="To be enabled in another PR for triage and debug")
def test_bias_generator(disable_tap):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.bias_generator(name)
    constraints = {
        "nbias_gen": [
            {
                "constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True, "identify_array": False,
                "fix_source_drain": False, "merge_series_devices": False, "merge_parallel_devices": False,
                "remove_dummy_devices": False, "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vcca"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vcca"]},
            {"constraint": "GroupBlocks", "instances": ["mp0"], "instance_name": "xmp0", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qp1"], "instance_name": "xqp1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["mp1"], "instance_name": "xmp1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["mn0"], "instance_name": "xmn0", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn1"], "instance_name": "xqn1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {
                "constraint": "Floorplan",
                "order": True,
                "symmetrize": False,
                "regions": [
                ["i0", "i6"],
                ["xmp0", "xqp1", "xmp1"],
                ["xmn0", "xqn1"],
                ["i9"]
                ]
            },
            {"constraint": "Order", "direction": "left_to_right", "instances": ["r0", "i0"]},
            {"constraint": "Order", "direction": "left_to_right", "instances": ["r0", "i9"]}
        ],
        "pbias_gen": [
            {
                "constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True, "identify_array": False,
                "fix_source_drain": False, "merge_series_devices": False, "merge_parallel_devices": False,
                "remove_dummy_devices": False, "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vcca"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vcca"]},
            {"constraint": "GroupBlocks", "instances": ["mp0"], "instance_name": "xmp0", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qp1"], "instance_name": "xqp1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["mn0"], "instance_name": "xmn0", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn1"], "instance_name": "xqn1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["mn1"], "instance_name": "xmn1", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {
                "constraint": "Floorplan",
                "order": True,
                "symmetrize": False,
                "regions": [
                ["i0", "i6"],
                ["xmn0", "xqn1", "xmn1"],
                ["xmp0", "xqp1"],
                ["i9"]
                ]
            },
            {"constraint": "Order", "direction": "left_to_right", "instances": ["r0", "i0"]},
            {"constraint": "Order", "direction": "left_to_right", "instances": ["r0", "i9"]}
        ],
        "folded_cascode_p": [
            {
                "constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True, "identify_array": False,
                "fix_source_drain": False, "merge_series_devices": False, "merge_parallel_devices": False,
                "remove_dummy_devices": False, "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vcca"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vcca"]},
            {"constraint": "GroupBlocks", "instances": ["qp4", "qp3"], "instance_name": "xqp43", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qp2", "qp1"], "instance_name": "xqp21", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn4", "qn3"], "instance_name": "xqn43", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn6", "qn5"], "instance_name": "xqn65", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 4}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn1", "qn2"], "instance_name": "xqn12", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "SameTemplate", "instances": ["qp5<0>", "qp5<1>"]},
            {"constraint": "SameTemplate", "instances": ["qp6<0>", "qp6<1>"]},
            {
                "constraint": "Floorplan",
                "order": True,
                "symmetrize": True,
                "regions": [
                ["xqn12"],
                ["qp6<0>", "xqn65", "qp6<1>"],
                ["qp5<0>", "xqn43", "qp5<1>"],
                ["xqp21"],
                ["xqp43"]
                ]
            }
        ],
        "folded_cascode_n": [
            {
                "constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True, "identify_array": False,
                "fix_source_drain": False, "merge_series_devices": False, "merge_parallel_devices": False,
                "remove_dummy_devices": False, "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vcca"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vcca"]},
            {"constraint": "GroupBlocks", "instances": ["qp4", "qp3"], "instance_name": "xqp43", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qp2", "qp1"], "instance_name": "xqp21", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn4", "qn3"], "instance_name": "xqn43", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn6", "qn5"], "instance_name": "xqn56", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn1", "qn2"], "instance_name": "xqn12", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 2}]}}}, 
            {"constraint": "SameTemplate", "instances": ["qp5<0>", "qp5<1>"]},
            {"constraint": "SameTemplate", "instances": ["qp6<0>", "qp6<1>"]},
            {
                "constraint": "Floorplan",
                "order": True,
                "symmetrize": True,
                "regions": [
                ["xqn56"],
                ["xqn43"],
                ["qp6<0>", "xqp21", "qp6<1>"],
                ["qp5<0>", "xqp43", "qp5<1>"],
                ["xqn12"]
                ]
            }
        ],
        name: [
            {
                "constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True, "identify_array": False,
                "fix_source_drain": False, "merge_series_devices": False, "merge_parallel_devices": False,
                "remove_dummy_devices": False, "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vccd", "vcca"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vccd", "vcca"]},
            {"constraint": "GroupBlocks", "instances": ["nand0", "nand1", "inv09"], "instance_name": "xdig"},
            {"constraint": "GroupBlocks", "instances": ["R0", "i12", "i21", "i13", "i20", "qn3"], "instance_name": "xoutp"},
            {"constraint": "GroupBlocks", "instances": ["R6", "i15", "i35", "i36", "i22", "i16"], "instance_name": "xoutn"},
            {"constraint": "GroupBlocks", "instances": ["i25", "i32"], "instance_name": "xbiasp"},
            {"constraint": "GroupBlocks", "instances": ["i24", "i27"], "instance_name": "xbiasn"},
            {
            "constraint": "Floorplan",
            "order": True,
            "symmetrize": False,
            "regions": [
                ["xdig"],
                ["xbiasp", "i0", "xoutp"],
                ["xbiasn", "i14", "xoutn"]
            ]
            }
          ]
        }
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, n=1, max_errors=4)
