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
    netlist = textwrap.dedent("""\
        mp29 v4 vbias2 v2 vccx p w=2.16e-6 m=1 nf=12
        mp33 vbias2 vbias2 vbias1 vccx p w=1.44e-6 m=1 nf=8
        """)
    netlist = f".subckt {name} vbias2 vccx\n"+ netlist + ".ends"
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
            assert key.startswith('PMOS') or key.startswith('DCL'), 'Incorrect subcircuit identification'

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
