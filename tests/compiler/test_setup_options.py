from os import name
import pathlib
import pytest
import pathlib
import shutil
import json
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context, List, Dict
from align.compiler.compiler import compiler_input, generate_hierarchy
from utils import ota_six, ota_six_flip, clean_data, build_example
import textwrap

pdk_path = (
    pathlib.Path(__file__).resolve().parent.parent.parent
    / "pdks"
    / "FinFET14nm_Mock_PDK"
)
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def test_ota_six():
    name = "CKT_OTA"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set(["CKT_OTA", "SCM_NMOS", "SCM_PMOS", "DP_NMOS_B"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_ota_swap():
    # check dran gate swap
    name = "CKT_OTA_1"
    netlist = ota_six_flip(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set(["CKT_OTA_1", "SCM_NMOS", "SCM_PMOS", "DP_NMOS_B"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_ota_dont_swap():
    # check dran gate swap
    name = "CKT_OTA_1"
    netlist = ota_six_flip(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        FIX_SOURCE_DRAIN = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set(["CKT_OTA_1", "SCM_NMOS", "SCM_PMOS"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_skip_digital():
    name = "CKT_OTA"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        DIGITAL = CKT_OTA
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set(["CKT_OTA"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_dont_use_lib_cell():
    name = "CKT_OTA"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        DONT_USE_LIB = DP_NMOS_B
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set(["CKT_OTA", "SCM_NMOS", "SCM_PMOS"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    clean_data(name)


def test_dont_const():
    name = "CKT_OTA"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        DONT_CONST = CKT_OTA
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    gen_const_path = out_path / "CKT_OTA.verilog.json"
    with open(gen_const_path, "r") as fp:
        gen_const = next(x for x in json.load(fp)["modules"] if x["name"] == "CKT_OTA")[
            "constraints"
        ]
        assert len(gen_const) == 0
    clean_data(name)


def test_dont_constrain_clk():
    # TODO Do not constrain clock connected devices
    name = "CKT_DUMMY1"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        CLOCK = vin
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass


def test_identify_array():
    # TODO Do not identify array when setup set as false
    name = "CKT_DUMMY2"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        IDENTIFY_ARRAY = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass


def test_merge_caps():
    # TODO Do not identify array when setup set as false
    name = "CKT_DUMMY3"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        MERGE_SYMM_CAPS = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass


def test_keep_duppy():
    # TODO Do not identify array when setup set as false
    name = "CKT_DUMMY4"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        KEEP_DUMMY = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass


def test_merge_series():
    # TODO Do not identify array when setup set as false
    name = "CKT_DUMMY5"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        MERGE_SERIES = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass


def test_merge_parallel():
    # TODO Do not identify array when setup set as false
    name = "CKT_DUMMY6"
    netlist = ota_six(name)
    setup = textwrap.dedent(
        """\
        POWER = vccx
        GND = vssx
        MERGE_PARALLEL = False
        """
    )
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    generate_hierarchy(example, name, out_path, False, pdk_path, False)
    clean_data(name)
    pass
