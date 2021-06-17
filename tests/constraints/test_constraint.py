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


def five_t_ota(a_path, name, constraints):
    netlist = f""".subckt {name} vin vip vop vccx vssx vbn
mp1 von von vccx vccx p nfin=4 nf=4 m=5
mp2 vop von vccx vccx p nfin=4 nf=4 m=5
mn1 von vip vcom vssx n nfin=4 nf=4 m=5
mn2 vop vin vcom vssx n nfin=4 nf=4 m=5
mn0 vmd vbn vssx vssx n nfin=4 nf=4 m=5
.ends {name}
"""
    netlist_setup = f""""""
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


def run_example(example, cleanup=True):

    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '-l','INFO']
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f"{example.name}: No results generated"
    
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(example)
    return(results)


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


def test_boundary_max_width():
    constraints = """[
    {"constraint": "HorizontalDistance", "abs_distance":0},
    {"constraint": "VerticalDistance",   "abs_distance":0},
    {"constraint": "Boundary", "subcircuit": "example_boundary_max_width", "max_width": 3.5}
]
"""
    name = "example_boundary_max_width"
    run_example(cascode_amplifier(my_dir, name, constraints))


def test_boundary_max_height():
    constraints = """[
    {"constraint": "HorizontalDistance", "abs_distance":0},
    {"constraint": "VerticalDistance",   "abs_distance":0},
    {"constraint": "Boundary", "subcircuit": "example_boundary_max_height", "max_height": 1.3}
]
"""
    name = "example_boundary_max_height"
    run_example(cascode_amplifier(my_dir, name, constraints))


def test_do_not_identify():
    constraints = """[
    {"constraint": "AlignInOrder", "line": "left", "instances": ["mp1", "mn1"]}
]
"""
    name = "example_do_not_identify"
    results = run_example(five_t_ota(my_dir, name, constraints), cleanup=False)

test_do_not_identify()