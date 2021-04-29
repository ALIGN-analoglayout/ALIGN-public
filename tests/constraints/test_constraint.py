import os
import pytest
import pathlib
from align.schema import constraint
from align.schema.checker import Z3Checker, CheckerError
import shutil
import align.pdk.finfet

my_dir = pathlib.Path(__file__).resolve().parent

pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent


def cascode_amplifier(a_path, name, constraints):
    netlist = f""".subckt {name} vin vop vcc vss nbs pbs
mp1 vop pbs vcc vcc p nfin=4 nf=4 m=5
mn1 vop nbs vmd vss n nfin=4 nf=4 m=5
mn0 vmd vin vss vss n nfin=4 nf=4 m=5
.ends {name}
"""
    netlist_setup = f"""POWER = 
GND = 
CLOCK =
DIGITAL =
"""
    example = a_path / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp' ,'w') as fp:
        fp.write(netlist)
    with open(example / f'{name}.setup' ,'w') as fp:
        fp.write(netlist_setup)
    with open(example / f'{name}.const.json' ,'w') as fp:
        fp.write(constraints)
    
    return example


def run_example(example):

    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '--check', '-l','INFO']
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f"{example.name}: No results generated"
    
    shutil.rmtree(run_dir)
    shutil.rmtree(example)


def test_aspect_ratio_min():
    constraints = """[
    {"constraint": "HorizontalDistance", "abs_distance":0},
    {"constraint": "VerticalDistance",   "abs_distance":0},
    {"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_min", "ratio_low": 3}
]
"""
    name = "example_aspect_ratio_min"
    run_example(cascode_amplifier(my_dir, name, constraints))

    
def test_aspect_ratio_max():
    constraints = """[
    {"constraint": "HorizontalDistance", "abs_distance":0},
    {"constraint": "VerticalDistance",   "abs_distance":0},
    {"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_max", "ratio_high": 1}
]
"""
    name = "example_aspect_ratio_max"
    run_example(cascode_amplifier(my_dir, name, constraints))

