import pathlib
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.graph import Graph
from align.schema import constraint
from align.schema.types import set_context, List, Dict
from align.compiler.create_array_hierarchy import array_hierarchy
from align.compiler.compiler import compiler_input, compiler_output
from align.compiler.find_constraint import add_or_revert_const, symmnet_device_pairs
from utils import clean_data, build_example, ring_oscillator
import textwrap

pdk_path = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
config_path =  pathlib.Path(__file__).resolve().parent.parent / 'files'
out_path = pathlib.Path(__file__).resolve().parent / 'Results'


def test_array_gen():
    name = 'RING_OSCILLATOR'
    netlist = ring_oscillator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    design_setup = {'POWER': ['VCCX'],
                    'GND': ['VSSX'],
                    'DIGITAL':list(),
                    'IDENTIFY_ARRAY':True,
                    'CLOCK': list()}
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert ckt, f"No ckt {name} found in library"
    array = array_hierarchy(ckt, design_setup)
    array.find_array('VO', ['VCCX', 'VSSX'])
    array_subckt = ckt_library.find('ARRAY_HIER_VO')
    assert array_subckt
    clean_data(name)
