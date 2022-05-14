import pathlib
import json
from align.schema import SubCircuit
from align.compiler.compiler import compiler_input, generate_hierarchy, annotate_library
from utils import ota_six, ota_six_flip, clean_data, build_example, get_test_id

pdk_path = (
    pathlib.Path(__file__).resolve().parent.parent.parent
    / "pdks"
    / "FinFET14nm_Mock_PDK"
)
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def test_ota_six():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    all_modules = set(['CKT_OTA', "SCM_NMOS", "SCM_PMOS", "DP_NMOS_B"])
    available_modules = set(
        ['_'.join(module.name.split('_')[:-1]) for module in ckt_lib if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_ota_swap():
    # check drain gate swap
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six_flip(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    all_modules = set(['CKT_OTA', 'SCM_NMOS', 'SCM_PMOS', 'DP_NMOS_B'])
    available_modules = set(
        ['_'.join(module.name.split('_')[:-1]) for module in ckt_lib if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_ota_dont_swap():
    # check drain gate swap
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six_flip(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "fix_source_drain": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    all_modules = set(['CKT_OTA_DONT', 'SCM_NMOS', 'SCM_PMOS', "NMOS_4T"])
    available_modules = set(
        ['_'.join(module.name.split('_')[:-1]) for module in ckt_lib if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_skip_digital():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "is_digital": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    all_modules = set([name])
    available_modules = set([module.name for module in ckt_lib if isinstance(module, SubCircuit)])
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_dont_use_lib_cell():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "DoNotUseLib", "libraries": ["DP_NMOS_B"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_lib, prim_lib = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    all_modules = set(['CKT_DONT_USE_LIB', 'SCM_NMOS', 'SCM_PMOS', "NMOS_4T"])
    available_modules = set(
        ['_'.join(module.name.split('_')[:-1]) for module in ckt_lib if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_dont_const():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "auto_constraint": False}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    gen_const_path = out_path / f'{name}.verilog.json'
    with open(gen_const_path, "r") as fp:
        gen_const = next(x for x in json.load(fp)['modules'] if x['name'] == name)["constraints"]
        gen_const = [c for c in gen_const if c['constraint'] != "group_blocks"]
        assert len(gen_const) == 3, f"{gen_const}"
    clean_data(name)


def test_dont_constrain_clk():
    # TODO Do not constrain clock connected devices
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ClockPorts", "ports": ["vin"]}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    clean_data(name)
    pass


def test_identify_array():
    # TODO Do not identify array when setup set as false
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "identify_array": False}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    clean_data(name)
    pass


def test_keep_duppy():
    # TODO Do not identify array when setup set as false
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    clean_data(name)
    pass


def test_merge_series():
    # TODO Do not identify array when setup set as false
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "merge_series_devices": False}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    clean_data(name)
    pass


def test_merge_parallel():
    # TODO Do not identify array when setup set as false
    name = f'ckt_{get_test_id()}'.upper()
    netlist = ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ConfigureCompiler", "merge_parallel_devices": False}
    ]
    example = build_example(name, netlist, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path)
    clean_data(name)
    pass
