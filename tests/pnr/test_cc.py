import textwrap
import pytest
from .utils import get_test_id, build_example, run_example

def test_cc_24():

    name = f'ckt_{get_test_id()}'

    netlist = textwrap.dedent(f"""\
       .subckt {name} o0 o1 i0 i1 vccx vssx
       mp0 o0 i0 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn0 o0 i0 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       mp1 o1 i1 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn1 o1 i1 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       c0 o0 vssx w=240 l=200
       c1 o1 vssx w=240 l=200
       .ends {name}
       """)

    constraints = [
        {
            "constraint": "PowerPorts",
            "ports": ["vccx"]
        },
        {
            "constraint": "GroundPorts",
            "ports": ["vssx"]
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp0", "mn0"],
            "name": "inv0"
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp1", "mn1"],
            "name": "inv1"
        },
        {
            "constraint": "GroupCaps",
            "instances": ["c0", "c1"],
            "name": "c0_c1",
            "unit_cap": "Cap_12f",
            "num_units": [2, 2],
            "dummy": False
        },
        {
            "constraint": "SymmetricBlocks",
            "direction": "V",
            "pairs": [["inv0", "inv1"], ["c0_c1"]]
        }
    ]

    example = build_example(name, netlist, constraints)

    run_example(example, cleanup=False, log_level='INFO', additional_args=["--skipGDS"])

def test_cc_36():

    name = f'ckt_{get_test_id()}'

    netlist = textwrap.dedent(f"""\
       .subckt {name} o0 o1 i0 i1 vccx vssx
       mp0 o0 i0 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn0 o0 i0 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       mp1 o1 i1 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn1 o1 i1 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       c0 o0 vssx w=360 l=200
       c1 o1 vssx w=360 l=200
       .ends {name}
       """)

    constraints = [
        {
            "constraint": "PowerPorts",
            "ports": ["vccx"]
        },
        {
            "constraint": "GroundPorts",
            "ports": ["vssx"]
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp0", "mn0"],
            "name": "inv0"
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp1", "mn1"],
            "name": "inv1"
        },
        {
            "constraint": "GroupCaps",
            "instances": ["c0", "c1"],
            "name": "c0_c1",
            "unit_cap": "Cap_12f",
            "num_units": [3, 3],
            "dummy": False
        },
        {
            "constraint": "SymmetricBlocks",
            "direction": "V",
            "pairs": [["inv0", "inv1"], ["c0_c1"]]
        }
    ]

    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False, log_level='INFO', additional_args=["--skipGDS"])

def test_cc_60():

    name = f'ckt_{get_test_id()}'

    netlist = textwrap.dedent(f"""\
       .subckt {name} o0 o1 i0 i1 vccx vssx
       mp0 o0 i0 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn0 o0 i0 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       mp1 o1 i1 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn1 o1 i1 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       c0 o0 vssx w=600 l=200
       c1 o1 vssx w=600 l=200
       .ends {name}
       """)

    constraints = [
        {
            "constraint": "PowerPorts",
            "ports": ["vccx"]
        },
        {
            "constraint": "GroundPorts",
            "ports": ["vssx"]
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp0", "mn0"],
            "name": "inv0"
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp1", "mn1"],
            "name": "inv1"
        },
        {
            "constraint": "GroupCaps",
            "instances": ["c0", "c1"],
            "name": "c0_c1",
            "unit_cap": "Cap_12f",
            "num_units": [5, 5],
            "dummy": False
        },
        {
            "constraint": "SymmetricBlocks",
            "direction": "V",
            "pairs": [["inv0", "inv1"], ["c0_c1"]]
        }
    ]

    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False, log_level='INFO', additional_args=["--skipGDS"], max_errors=1)

@pytest.mark.skip("Coredumping")
def test_cc_with_dummies():

    name = f'ckt_{get_test_id()}'

    netlist = textwrap.dedent(f"""\
       .subckt {name} o0 o1 i0 i1 vccx vssx
       mp0 o0 i0 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn0 o0 i0 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       mp1 o1 i1 vccx vccx p w=270e-9 l=20e-9 nfin=6 nf=2
       mn1 o1 i1 vssx vssx n w=270e-9 l=20e-9 nfin=6 nf=2
       c0 o0 vssx w=240 l=200
       c1 o1 vssx w=240 l=200
       .ends {name}
       """)

    constraints = [
        {
            "constraint": "PowerPorts",
            "ports": ["vccx"]
        },
        {
            "constraint": "GroundPorts",
            "ports": ["vssx"]
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp0", "mn0"],
            "name": "inv0"
        },
        {
            "constraint": "GroupBlocks",
            "instances": ["mp1", "mn1"],
            "name": "inv1"
        },
        {
            "constraint": "GroupCaps",
            "instances": ["c0", "c1"],
            "name": "c0_c1",
            "unit_cap": "Cap_12f",
            "num_units": [2, 2],
            "dummy": True
        },
        {
            "constraint": "SymmetricBlocks",
            "direction": "V",
            "pairs": [["inv0", "inv1"], ["c0_c1"]]
        }
    ]

    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False, log_level='INFO', additional_args=["--skipGDS"])
