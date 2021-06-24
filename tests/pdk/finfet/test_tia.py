import pytest
try:
    from .helper import *
except:
    from helper import *


def tia(name):
    netlist = f"""*
.subckt pcell_tfr_0 a b
xi0 a b tfr_prim w=1e-6 l=1e-6
.ends pcell_tfr_0
.subckt {name} vin vop vccx vss
mp0 vop vin vccx vccx p nfin=4 nf=4 m=4
mn0 vop vin vssx vssx n nfin=4 nf=4 m=4
xi0 vin vop pcell_tfr_0
.ends {name}
"""
    netlist_setup = f""""""
    return netlist, netlist_setup
    

def test_tia():
    constraints = """[]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = tia(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1)

