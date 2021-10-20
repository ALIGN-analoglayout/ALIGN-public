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
pdk_path = (
    pathlib.Path(__file__).resolve().parent.parent.parent
    / "pdks"
    / "FinFET14nm_Mock_PDK"
)
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def ota_six(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 von vin tail vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """
    )
    return netlist


def ota_six_flip(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 tail vin von vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """
    )
    return netlist


def ring_oscillator(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt inverter vi vo vssx vccx
        mp0 vo vi vcccx vccx p nfin=4 l=40n m=2
        mn0 vo vi vssx vssx n nfin=4 l=40n m=2
        .ends inverter
        .subckt {name} vo vccx vssx
        xi0 vo n1 vssx vccx inverter
        xi1 n1 n2 vssx vccx inverter
        xi2 n2 n3 vssx vccx inverter
        xi3 n3 n4 vssx vccx inverter
        xi4 n4 vo vssx vccx inverter
        .ends {name}
    """
    )
    return netlist

def ring_oscillator_flat(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} vo vccx vssx
        mp0 vo n1 vccx vccx p nfin=4 l=40n m=2
        mn0 vo n1 vssx vssx n nfin=4 l=40n m=2
        mp1 n1 n2 vccx vccx p nfin=4 l=40n m=2
        mn1 n1 n2 vssx vssx n nfin=4 l=40n m=2
        mp2 n2 n3 vccx vccx p nfin=4 l=40n m=2
        mn2 n2 n3 vssx vssx n nfin=4 l=40n m=2
        mp3 n3 n4 vccx vccx p nfin=4 l=40n m=2
        mn3 n3 n4 vssx vssx n nfin=4 l=40n m=2
        mp4 n4 v0 vccx vccx p nfin=4 l=40n m=2
        mn4 n4 v0 vssx vssx n nfin=4 l=40n m=2
        .ends {name}
    """
    )
    return netlist
def linear_equalizer(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} vmirror_ctle s0_ctle s3_ctle vin1 vin2 vout_ctle1 vout_ctle2 vps vgnd
        .param nfpf_cm=72 nfpf_dp=48 nfpf_sw=48 Rsw=100 Csw=24f rl=800
        M0 vout_ctle2 vin2 net8 vgnd nfet p1=48
        M1 vout_ctle1 vin1 net5 vgnd nfet p1=48
        M4 vmirror_ctle vmirror_ctle vgnd vgnd nfet p1=nfpf_cm
        M3 net5 vmirror_ctle vgnd vgnd nfet p1=nfpf_cm
        M2 net8 vmirror_ctle vgnd vgnd nfet p1=nfpf_cm
        R1 vps vout_ctle2 resistor r=rl
        R0 vps vout_ctle1 resistor r=rl
        C4 net021 net8 capacitor c=Csw
        C3 net5 net022 capacitor c=Csw
        R4 net5 net016 resistor r=Rsw
        R3 net015 net8 resistor r=Rsw
        MN9 net021 s3_ctle net022 vgnd nfet l=0.014u nfin=nfpf_sw
        MN6 net015 s0_ctle net016 vgnd nfet l=0.014u nfin=nfpf_sw
        .ends {name}
    """
    )
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
    with open(example / f"{name}.sp", "w") as fp:
        fp.write(netlist)
    with open(example / f"{name}.setup", "w") as fp:
        fp.write(netlist_setup)
    with open(example / f"{name}.const.json", "w") as fp:
        fp.write(json.dumps(constraints, indent=2))
    return example / (name + ".sp")
