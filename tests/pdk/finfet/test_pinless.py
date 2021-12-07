import textwrap
try:
    from .utils import get_test_id, build_example, run_example
except ImportError:
    from utils import get_test_id, build_example, run_example

cleanup = False


def test_pinless():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        xi0 vccx vop tfr_prim w=1e-6 l=1e-6 p1=pwr
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False},
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "DoNotRoute", "nets": ["VCCX", "VSSX"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)
