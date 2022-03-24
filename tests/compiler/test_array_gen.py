import pathlib
from align.schema import SubCircuit
from align.schema import constraint
from align.compiler.find_constraint import FindConst
from align.schema.types import set_context
from align.compiler.create_array_hierarchy import process_arrays
from align.compiler.compiler import compiler_input, annotate_library
from utils import clean_data, build_example, ring_oscillator, array_limit, array_pair
from utils import ring_oscillator_flat, variable_gain_amplifier_equal, get_test_id

pdk_path = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
config_path = pathlib.Path(__file__).resolve().parent.parent / 'files'
out_path = pathlib.Path(__file__).resolve().parent / 'Results'


def test_array_gen_ro():
    name = f'ckt_{get_test_id()}'
    netlist = ring_oscillator(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    ckt = ckt_lib.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == ['XI0', 'XI1', 'XI2', 'XI3', 'XI4']
    array_cl.add_align_block_const()
    with set_context(ckt.constraints):
        x = constraint.Align(line="h_center", instances=array1)
    assert ckt.constraints == [x]
    clean_data(name)


def test_array_gen_ro_off():
    name = f'ckt_{get_test_id()}'
    netlist = ring_oscillator(name)
    constraints = [{"constraint": "ConfigureCompiler", "identify_array": False}
                   ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    ckt = ckt_lib.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == None
    clean_data(name)


def test_array_gen_ro_skip_digital():
    name = f'ckt_{get_test_id()}'
    netlist = ring_oscillator(name)
    constraints = [{"constraint": "ConfigureCompiler", "is_digital": True}
                   ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    ckt = ckt_lib.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == None
    clean_data(name)

def test_array_gen_ro_fh():
    name = f'ckt_{get_test_id()}'
    netlist = ring_oscillator_flat(name)
    constraints = [
        {"constraint": "DoNotUseLib", "libraries": ["STAGE2_INV"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_lib.find(name)
    FindConst(ckt)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == ['X_MN0_MP0', 'X_MN1_MP1', 'X_MN2_MP2', 'X_MN3_MP3', 'X_MN4_MP4']
    array_cl.add_align_block_const()
    with set_context(ckt.constraints):
        x = constraint.Align(line="h_center", instances=array1)
    assert ckt.constraints[-1] == x
    clean_data(name)


def test_array_gen_ro_f():
    name = f'ckt_{get_test_id()}'
    netlist = ring_oscillator_flat(name)
    constraints = [
        {"constraint": "DoNotUseLib", "libraries": ["STAGE2_INV", "INV", "DP_PMOS", "DP_NMOS"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    ckt = ckt_lib.find(name)
    assert ckt, f"No ckt {name} found in library"
    array_cl = process_arrays(ckt, dict())
    array1 = array_cl.find_array('VCCX', ['VSSX'])
    assert array1 == [['X_MP0', 'X_MN0'], ['X_MP1', 'X_MN1'], ['X_MP2', 'X_MN2'], ['X_MP3', 'X_MN3'], ['X_MP4', 'X_MN4']]
    array_cl.add_align_block_const()
    array_cl.add_new_array_hier()
    assert ckt.get_element("X_ARRAY_HIER_VCCX")
    assert ckt_lib.find("ARRAY_HIER_VCCX")
    assert ckt_lib.find("ARRAY_TEMPLATE"), f"{set([inst.name for inst in ckt_lib.find('ARRAY_TEMPLATE').elements])}"
    assert set([inst.name for inst in ckt_lib.find("ARRAY_TEMPLATE").elements]) == {'X_MP0', 'X_MN0'}
    array_insts = ['X_ARRAY_TEMPLATE', 'X_ARRAY_TEMPLATE1', 'X_ARRAY_TEMPLATE2', 'X_ARRAY_TEMPLATE3', 'X_ARRAY_TEMPLATE4']
    assert [inst.name for inst in ckt_lib.find("ARRAY_HIER_VCCX").elements] == array_insts
    clean_data(name)


def test_array_vga_equal():
    name = f'ckt_{get_test_id()}'
    netlist = variable_gain_amplifier_equal(name)
    constraints = list()
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    ckt = ckt_lib.find(name)
    assert ckt, f"No ckt {name} found in library"
    FindConst(ckt)
    all_arrays = [module.name for module in ckt_lib if isinstance(module, SubCircuit) and 'ARRAY' in module.name]
    ARRAY_HIER = ckt_lib.find("ARRAY_HIER_VOUT_VGA1")
    assert ARRAY_HIER, f"ARRAY_HIER_VOUT_VGA1 not found in {all_arrays}"
    TEMPLATE = ckt_lib.find("ARRAY_TEMPLATE")
    assert TEMPLATE, f"TEMPLATE not found in {all_arrays}"
    insts = [inst.name for inst in TEMPLATE.elements]
    assert set(insts) == {'X_M00_M01', 'X_MSW0'}
    clean_data(name)

def test_array_limit():
    name = f'ckt_{get_test_id()}'
    netlist = array_limit(name)
    constraints = [
        {"constraint": "DoNotUseLib", "libraries": ["STAGE2_INV", "INV", "DP_NMOS", "DP_NMOS_B"]}
    ]
    example = build_example(name, netlist, constraints)
    cktlib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(cktlib, prim_lib)
    FindConst(cktlib.find(name))
    all_modules = {module.name for module in cktlib if isinstance(module, SubCircuit) and len(module.elements)>1 }
    assert all_modules == {name.upper()}
    align_const = cktlib.find(name).constraints.dict()['__root__'][1]
    assert set(align_const["instances"]) == {"X_MN1", "X_MN2", "X_MN3", "X_MN4", "X_MN5", "X_MN6",
                                         "X_MN7", "X_MN8", "X_MN9", "X_MN10", "X_MN11", "X_MN12"}
    clean_data(name)



