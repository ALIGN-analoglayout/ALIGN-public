import pytest
import textwrap
import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits

cleanup = False


def test_buf_1():
    name = f'ckt_{get_test_id()}'
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_CONST = {name}
        """)
    netlist = textwrap.dedent(f"""\
    .subckt buf vi vo vccx vssx
    mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
    mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx buf
    xi1 v1 v2 vccx vssx buf
    xi2 v2 v3 vccx vssx buf
    xi3 v3 v4 vccx vssx buf
    xi4 v4 vo vccx vssx buf
    .ends {name}
    """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


def test_ro_1():
    name = f'ckt_{get_test_id()}'
    setup = textwrap.dedent("""\
        DONT_CONST = {name}
        """)
    netlist = textwrap.dedent(f"""\
    .subckt ro_stage vi vo vccx vssx
    mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
    mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
    .ends
    .subckt {name} vo vccx vssx
    xi0 vo v1 vccx vssx ro_stage
    xi1 v1 v2 vccx vssx ro_stage
    xi2 v2 v3 vccx vssx ro_stage
    xi3 v3 v4 vccx vssx ro_stage
    xi4 v4 vo vccx vssx ro_stage
    .ends {name}
    """)
    constraints = {
        'ro_stage': [
            {"constraint": "Order", "direction": "left_to_right", "instances": ["mn0", "mp0"]},
        ],
        name: [
            {"constraint": "Order", "direction": "left_to_right", "instances": [f'xi{k}' for k in range(5)]},
        ]
    }
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=cleanup)

    with (run_dir / '3_pnr' / 'inputs' / 'RO_STAGE.pnr.const.json').open('rt') as fp:
        d = json.load(fp)
        assert len(d['constraints']) > 0, 'Where is the order constraint???'
