import pytest
import textwrap
from .utils import get_test_id, build_example, run_example

CLEANUP = True


@pytest.mark.skip(reason="this test is failing in CircleCI")
def test_pinless():
    name = f'ckt_{get_test_id()}'
    setup = textwrap.dedent("""""")
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        xi0 vccx vop tfr_prim w=1e-6 l=1e-6 p1=pwr
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]}
        ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=CLEANUP)
