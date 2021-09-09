from os import name
import pathlib
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context, List, Dict
from align.compiler.compiler import compiler_input, generate_hierarchy

import textwrap

my_dir = pathlib.Path(__file__).resolve().parent
pdk_path = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
config_path =  pathlib.Path(__file__).resolve().parent.parent / 'files'
out_path = pathlib.Path(__file__).resolve().parent / 'Results'

def ota_six(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 von vin tail vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """)
    return netlist

def ota_six_flip(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 tail vin von vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """)
    return netlist

def clean_data(name):
    example = my_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)

def build_example(name, netlist, netlist_setup, constraints):
    example = my_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp', 'w') as fp:
        fp.write(netlist)
    with open(example / f'{name}.setup', 'w') as fp:
        fp.write(netlist_setup)
    with open(example / f'{name}.const.json', 'w') as fp:
        fp.write(json.dumps(constraints, indent=2))
    return example / (name+'.sp')

