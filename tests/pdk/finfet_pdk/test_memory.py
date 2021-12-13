import pytest
import textwrap
import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except ImportError:
    from utils import get_test_id, build_example, run_example
    import circuits

cleanup = False

@pytest.mark.skip(reason="Only needed for debugging memory leaks")
def test_cmp_0():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=cleanup)


@pytest.mark.skip(reason="Only needed for debugging memory leaks")
def test_cmp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_CONST = {name}
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn", "invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"], ["invn", "invp"], ["mp9", "mp10"], ["mp7", "mp8"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 1, "ratio_high": 2}
    ]
    example = build_example(name, netlist, setup, constraints)

    run_example(example, cleanup=cleanup)

    # run_example(example, cleanup=cleanup,
    #             additional_args=['--flow_stop', '2_primitives'])

    # run_example(example, cleanup=cleanup,
    #             additional_args=['--flow_stop', '3_pnr:prep', '--router_mode', 'no_op'])
