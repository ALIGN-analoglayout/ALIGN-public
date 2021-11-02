import pathlib
import pytest
import pathlib
from align.schema.graph import Graph
from align.schema import constraint
from align.schema.types import set_context
from align.compiler.compiler import compiler_input
from align.compiler.find_constraint import add_symmetry_const, symmnet_device_pairs
from utils import clean_data, build_example, ota_six

align_home = pathlib.Path(__file__).resolve().parent.parent.parent
pdk_path = align_home / "pdks" / "FinFET14nm_Mock_PDK"
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def test_symm_net():
    name = 'CKT_OTA_SYMM_NET'
    netlist = ota_six(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        DIGITAL = {name}
        """)
    constraints = [
        {"constraint": "IsDigital", "isTrue": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    assert len(ckt.elements) == 6
    G = Graph(ckt)
    pairs, pinsA, pinsB = symmnet_device_pairs(G,'VIN','VIP', list(),None, True)
    assert pairs == {'VIN': 'VIP', 'MN4': 'MN3'}
    assert pinsA == ['MN4/G', 'VIN']
    assert pinsB == ['MN3/G', 'VIP']
    pairs, pinsA, pinsB = symmnet_device_pairs(G,'VIN','VIP', [{'MN3', 'MN4'}],None)
    assert pairs == {'VIN': 'VIP', 'MN4': 'MN3'}
    pairs, pinsA, pinsB = symmnet_device_pairs(G,'VIN','VIP', ['MN3'],None)
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", ["MN4"], None)
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", list(), ["MN4"])
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VIP", list(), ["MN3"])
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "IBIAS", "TAIL", list(), ["MN3"])
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VON", "VOP", list(), ["MN3"])
    assert pairs == None
    pairs, pinsA, pinsB = symmnet_device_pairs(G, "VIN", "VON", list(), ["MN3"])
    assert pairs == None
    clean_data(name)


def test_add_symmetry_const():
    name = 'CKT_OTA_ADD_SYMMETRY_CONST'
    netlist = ota_six(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        DIGITAL = {name}
        """)
    constraints = [
        {"constraint": "IsDigital", "isTrue": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    ckt = ckt_library.find(name)
    insts = {inst.name for inst in ckt.elements}
    assert insts == {"MN1", "MN2", "MN3", "MN4", "MP5", "MP6"}
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
    assert len(ckt.constraints) == 2
