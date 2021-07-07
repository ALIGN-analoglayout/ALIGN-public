import os
import json
import pathlib
import pytest
import shutil
import align.pdk.finfet
try:
    from .helper import *
except:
    from helper import *

pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent

def tia(name):
    netlist = f"""*
.subckt pcell_tfr_0 a b
xi0 a b tfr_prim w=1e-6 l=1e-6
.ends pcell_tfr_0
.subckt {name} vin vop vccx vss
mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
xi0 vin vop pcell_tfr_0
.ends {name}
"""
    netlist_setup = f""""""
    return netlist, netlist_setup
    

def test_dependencies():
    constraints = """[]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = tia(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    # run_example(example, n=1, cleanup=False)

    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir)]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f"{example.name}: No results generated"
    
    with (run_dir / '2_primitives' / '__primitives__.json').open( 'rt') as fp:
        primitives = json.load(fp)    
    assert 'metadata' in primitives['tfr_prim_l_1e6_w_1e6'], f'Metadata not passed'

    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.placement_verilog.json').open( 'rt') as fp:
        placement = json.load(fp)

    shutil.rmtree(run_dir)
    shutil.rmtree(example)

