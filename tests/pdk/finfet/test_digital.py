
import pytest
import textwrap
import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example, plot_sa_cost, plot_sa_seq
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example, plot_sa_cost, plot_sa_seq
    import circuits

cleanup = False


def test_dig_1():
    name = f'ckt_{get_test_id()}'
    setup = textwrap.dedent("""\
        DONT_CONST = {name}
        """)
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
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=cleanup)

    # with (run_dir / '3_pnr' / 'inputs' / 'RO_STAGE.pnr.const.json').open('rt') as fp:
    #     d = json.load(fp)
    #     assert len(d['constraints']) > 0, 'Where is the order constraint???'