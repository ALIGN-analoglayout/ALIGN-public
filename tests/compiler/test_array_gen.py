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

pdk_path = (
    pathlib.Path(__file__).resolve().parent.parent.parent
    / "pdks"
    / "FinFET14nm_Mock_PDK"
)
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def test_array_gen():
    name = "CKT_OTA"
    netlist = ring_oscillator(name)
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
    ckt = ckt_library.find("CKT_OTA")
    G = Graph(ckt)
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", list(), None)
    assert pairs == {"VIN": "VIP", "MN4": "MN3"}
    assert pinsA == ["MN4/G", "VIN"]
    assert pinsB == ["MN3/G", "VIP"]
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", ["MN3", "MN4"], None)
    assert pairs == {"VIN": "VIP", "MN4": "MN3"}
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", ["MN3"], None)
    assert pairs == None

    clean_data(name)
