import pathlib
from re import template
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library, instance, library
from align.schema.graph import Graph
from align.schema import constraint
from align.compiler.find_constraint import FindConst
from align.schema.types import set_context, List, Dict
from align.compiler.create_array_hierarchy import process_arrays
from align.compiler.compiler import compiler_input, compiler_output
from utils import clean_data, build_example, ring_oscillator, ring_oscillator_flat, variable_gain_amplifier_equal
import textwrap

pdk_path = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
config_path =  pathlib.Path(__file__).resolve().parent.parent / 'files'
out_path = pathlib.Path(__file__).resolve().parent / 'Results'


def test_array_gen_ro():
    name = 'RING_OSCILLATOR'
    netlist = ring_oscillator(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == ['XI0', 'XI1', 'XI2', 'XI3', 'XI4']
    array_cl.add_align_block_const()
    with set_context(ckt.constraints):
        x = constraint.Align(line="h_center", instances=array1)
    assert ckt.constraints == [x]
    clean_data(name)


def test_array_gen_rofH():
    name = 'RING_OSCILLATOR_FLAT'
    netlist = ring_oscillator_flat(name)
    constraints =[
        {"constraint": "DoNotUseLib", "libraries": ["STAGE2_INV"]}
        ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == ['X_INV_MN0_MP0','X_INV_MN1_MP1','X_INV_MN2_MP2','X_INV_MN3_MP3','X_INV_MN4_MP4']
    array_cl.add_align_block_const()
    with set_context(ckt.constraints):
        x = constraint.Align(line="h_center", instances=array1)
    assert ckt.constraints[-1] == x
    clean_data(name)


def test_array_gen_rof():
    name = 'RING_OSCILLATOR_FLAT'
    netlist = ring_oscillator_flat(name)
    constraints =[
        {"constraint": "DoNotUseLib", "libraries": ["STAGE2_INV", "INV", "DP_PMOS", "DP_NMOS"]}
        ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == [['MP0', 'MN0'], ['MP1', 'MN1'], ['MP2', 'MN2'], ['MP3', 'MN3'], ['MP4', 'MN4']]
    array_cl.add_align_block_const()
    array_cl.add_new_array_hier()
    assert ckt.get_element("X_ARRAY_HIER_VCCX")
    assert ckt_library.find("ARRAY_HIER_VCCX")
    assert ckt_library.find("ARRAY_TEMPLATE"), f"{set([inst.name for inst in ckt_library.find('ARRAY_TEMPLATE').elements])}"
    assert set([inst.name for inst in ckt_library.find("ARRAY_TEMPLATE").elements]) == {'MP0', 'MN0'}
    array_insts = ['X_ARRAY_TEMPLATE', 'X_ARRAY_TEMPLATE1', 'X_ARRAY_TEMPLATE2', 'X_ARRAY_TEMPLATE3', 'X_ARRAY_TEMPLATE4']
    assert [inst.name for inst in ckt_library.find("ARRAY_HIER_VCCX").elements] == array_insts
    clean_data(name)

def test_array_vga_equal():
    name = 'VGA_EQUAL'
    netlist = variable_gain_amplifier_equal(name)
    constraints = list()
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert ckt, f"No ckt {name} found in library"
    FindConst(ckt)
    all_arrays = [module.name for module in ckt_library if isinstance(module, SubCircuit) and 'ARRAY' in module.name]
    ARRAY_HIER = ckt_library.find("ARRAY_HIER_VOUT_VGA1")
    assert ARRAY_HIER, f"\ ARRAY_HIER_VOUT_VGA1 not found in {all_arrays}"
    TEMPLATE = ckt_library.find("ARRAY_TEMPLATE")
    assert TEMPLATE, f"\TEMPLATE not found in {all_arrays}"
    insts = [inst.name for inst in TEMPLATE.elements]
    assert set(insts) == {'X_DP_NMOS_B_M00_M01', 'MSW0'}
    clean_data(name)