import pathlib
import pytest
from align.schema.graph import Graph
from align.schema import constraint
from align.schema.types import set_context
from align.compiler.util import get_ports_weight
from align.compiler.compiler import compiler_input, annotate_library
from align.compiler.find_constraint import add_or_revert_const, symmnet_device_pairs, recursive_start_points, add_symmetry_const
from utils import clean_data, build_example, ota_six, get_test_id, ota_dummy

align_home = pathlib.Path(__file__).resolve().parent.parent.parent
pdk_path = align_home / "pdks" / "FinFET14nm_Mock_PDK"
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def test_symm_net():
    name = f'ckt_{get_test_id()}'
    netlist = ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "is_digital": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    G = Graph(ckt)
    pairs, pinsA, pinsB = symmnet_device_pairs(G, 'VIN', 'VIP', list(), None, True)
    assert pairs == {'VIN': 'VIP', 'MN4': 'MN3'}
    assert pinsA == ['MN4/G', 'VIN']
    assert pinsB == ['MN3/G', 'VIP']
    pairs, pinsA, pinsB = symmnet_device_pairs(G, 'VIN', 'VIP', [{'MN3', 'MN4'}], None)
    assert pairs == {'VIN': 'VIP', 'MN4': 'MN3'}
    pairs, pinsA, pinsB = symmnet_device_pairs(G, 'VIN', 'VIP', ['MN3'], None)
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", ["MN4"], None)
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", list(), ["MN4"])
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", list(), ["MN3"])
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "IBIAS", "TAIL", list(), ["MN3"])
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VON", "VOP", list(), ["MN3"])
    assert pairs is None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VON", list(), ["MN3"])
    assert pairs is None
    clean_data(name)


def test_add_symmetry_const():
    name = f'ckt_{get_test_id()}'
    netlist = ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "is_digital": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    with set_context(ckt.constraints):
        x = constraint.SymmetricBlocks(direction="V", pairs=[["MN4", "MN3"]])
    const_pairs = {"MN4": "MN3"}  # skip dictionary element
    with pytest.raises(KeyError):
        add_or_revert_const(const_pairs, ckt.constraints, list())
    assert len(ckt.constraints) == 1
    const_pairs = [["MN4", "MN3"]]
    add_or_revert_const(const_pairs, ckt.constraints, list())
    assert len(ckt.constraints) == 2
    assert ckt.constraints[1] == x
    const_pairs = [["MN4", "MN5"]]  # Skip unequal size
    add_or_revert_const(const_pairs, ckt.constraints, list())
    assert len(ckt.constraints) == 2
    const_pairs = [["VIN", "VIP"]]  # Skip net
    add_or_revert_const(const_pairs, ckt.constraints, list())
    assert len(ckt.constraints) == 2, f"skip nets from symblock constraints {const_pairs}"
    const_pairs = [["MP3", "MP4"]]  # instances do not exist
    add_or_revert_const(const_pairs, ckt.constraints, list())
    assert len(ckt.constraints) == 2, f"skip instances who does not exist {const_pairs}"
    clean_data(name)


def test_match_start_points():
    name = f'ckt_{get_test_id()}'
    netlist = ota_six(name)
    constraints = [
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    graph = Graph(ckt)
    match_pairs = dict()
    stop_points = {'IBIAS', 'TAIL', 'VCCX', 'VSSX', 'VON', 'VOP'}
    ports_weight = get_ports_weight(graph)
    recursive_start_points(graph, match_pairs, stop_points, 'VIN', 'VIP', ports_weight)
    assert match_pairs[('VIN', 'VIP')] == {'MN4': 'MN3', 'VIN': 'VIP'}


def test_filter_duplicate_instances():
    name = f'ckt_{get_test_id()}'
    netlist = ota_six(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    add = add_symmetry_const(ckt, dict(), set(), [], None)
    pairs = [['MN3', 'MN4'], ['VIN', 'VIP'], ['MN4', 'MN4']]
    mpairs = add.filter_symblock_const(pairs)
    assert mpairs == [['MN3', 'MN4']]


def test_symmnet_filters():
    name = f'ckt_{get_test_id()}'
    netlist = ota_six(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    pairs = {1: {'MN3': 'MN4', 'VIN': 'VIP', 'MN4': 'MN4'}}
    add = add_symmetry_const(ckt, pairs, set(), [], None)
    add.loop_through_pairs()
    assert ckt.constraints[0].pairs == [['MN3', 'MN4']]


def test_filter_dummy():
    name = f'ckt_{get_test_id()}'
    netlist = ota_dummy(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library, primitive_library = compiler_input(example, name, pdk_path, config_path)
    annotate_library(ckt_library, primitive_library)
    ckt = ckt_library.find(name)
    add = add_symmetry_const(ckt, dict(), set(), [], None)
    pairs = [['X_MN3_MN4', 'X_MN3_MN4'], ['X_MN3_DUMMY', 'X_MN4_DUMMY']]
    mpairs = add.filter_symblock_const(pairs)
    assert mpairs == [['X_MN3_MN4'], ['X_MN3_DUMMY', 'X_MN4_DUMMY']]
