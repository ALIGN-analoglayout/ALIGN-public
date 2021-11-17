import json
import textwrap
from align.pdk.finfet import CanvasPDK
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_aspect_ratio_low():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_min", "ratio_low": 3}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_aspect_ratio_high():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_max", "ratio_high": 1}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_boundary_max_width():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "Boundary", "subcircuit": "example_boundary_max_width", "max_width": 3.5}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_boundary_max_height():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "Boundary", "subcircuit": "example_boundary_max_height", "max_height": 1.3}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_do_not_identify():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_five(name)
    constraints = [{"constraint": "AlignInOrder", "line": "left", "instances": ["mp1", "mn1"]}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_order_abut():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["ccp"], ["ccn"], ["dp"], ["mn0"], ["invn", "invp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.5, "ratio_high": 1.5},
        {"constraint": "Order", "abut": True, "direction": "left_to_right", "instances": ["invn", "invp"]}
    ]
    example = build_example(name, netlist, constraints)

    run_example(example)


def test_align_top_right():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=8
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=6
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=4
        .ends {name}
        """)
    constraints = [
        {"constraint": "AlignInOrder", "direction": "vertical", "line": "right", "instances": ["mn0", "mn1"]},
        {"constraint": "AlignInOrder", "direction": "horizontal", "line": "top", "instances": ["mn1", "mp1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_align_center():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=8
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=6
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=16
        .ends {name}
        """)
    constraints = [
        {"constraint": "AlignInOrder", "direction": "vertical", "line": "center", "instances": ["mn0", "mn1", "mp1"]}
        ]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_donotroute():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt inv vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt {name} vo vccx vssx
        xi0 vo v1 vccx vssx inv
        xi1 v1 v2 vccx vssx inv
        .ends
        """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["v1", "vccx"]}
        ]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False)

    with (run_dir / '3_pnr' / f'{name.upper()}_0.json').open('rt') as fp:
        d = json.load(fp)

        cv = CanvasPDK()
        cv.terminals = d['terminals']
        cv.gen_data(run_drc=True, run_pex=False)
        assert cv.drc.num_errors > 0, f'Layout should have opens'
