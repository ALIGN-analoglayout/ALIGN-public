import pathlib
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.graph import Graph
from align.schema import constraint
from align.schema.types import set_context, List, Dict
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
        DIGITAL = ring_oscillator
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find('RING_OSCILLATOR')
    G = Graph(ckt)

    clean_data(name)
