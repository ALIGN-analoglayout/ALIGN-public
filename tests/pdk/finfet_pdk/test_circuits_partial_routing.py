import pytest
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits

CLEANUP = True
BYPASS_ERRORS = True


@pytest.fixture
def partial_routing(monkeypatch):
    monkeypatch.setenv('PARTIAL_ROUTING', '1')

# TODO: Revise all of the tests below


def test_cmp_vanilla_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    # TODO: Reduce max_errors to 0 in the next PR
    run_example(example, cleanup=CLEANUP, max_errors=6 if not BYPASS_ERRORS else 3)


def test_cmp_fp1_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
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
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["xdp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["xccp"], ["xccn"], ["xinvn", "xinvp"], ["mp9", "mp10"], ["mp7", "mp8"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "xdp"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["xdp", "xccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 1, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, area=4e10, max_errors=5 if not BYPASS_ERRORS else 0)


def test_cmp_fp2_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
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
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, area=5e9, max_errors=1 if not BYPASS_ERRORS else 0)


def test_ota_six_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xg1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xg2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xg3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xg3", "xg2", "xg1"]},
        {"constraint": "MultiConnection", "nets": ["tail"], "multiplier": 4},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, max_errors=1 if not BYPASS_ERRORS else 0)


def test_cs_1_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=180e-9 nf=4 m=1
        mn0 vop vin vssx vssx n w=180e-9 nf=4 m=1
        .ends {name}
        """)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, max_errors=1 if not BYPASS_ERRORS else 0)


def test_cs_2_pr(partial_routing):
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=180e-9 nf=4 m=2
        mn0 vop vin vssx vssx n w=180e-9 nf=4 m=2
        .ends {name}
        """)
    constraints = [{"constraint": "MultiConnection", "nets": ["vop"], "multiplier": 2}]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, max_errors=1 if not BYPASS_ERRORS else 0)
