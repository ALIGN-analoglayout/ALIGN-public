import json
import shutil
import pytest
import textwrap
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_USE_CELLS = CASCODED_CMC_NMOS CMB_PMOS_2 LSB_PMOS_2 LSB_NMOS_2
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '1_topology' / '__primitives__.json').open('rt') as fp:
        primitives = json.load(fp)
        print(primitives)

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_2():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent("""\
        mp29 v4 vbias2 v2 vccx p w=2.16e-6 m=1 nf=12
        mp33 vbias2 vbias2 vbias1 vccx p w=1.44e-6 m=1 nf=8
        """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '1_topology' / '__primitives__.json').open('rt') as fp:
        primitives = json.load(fp)
        for key, _ in primitives.items():
            assert key.startswith('Switch') or key.startswith('DCL'), 'Incorrect subcircuit identification'

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
