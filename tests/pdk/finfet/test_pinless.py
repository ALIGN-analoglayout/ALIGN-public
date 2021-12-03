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


def test_pinless():
    name = f'ckt_{get_test_id()}'
    setup = textwrap.dedent("""""")
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        xi0 vccx vop tfr_prim w=1e-6 l=1e-6 p1=pwr
        mn0 vo vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]}
        ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)
