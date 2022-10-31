import pathlib
import pytest
from align.compiler.compiler import compiler_input, annotate_library
from align.schema import SubCircuit


@pytest.fixture
def ckt(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / (cn + ".sp")
    ckt_lib, prim_lib = compiler_input(test_path, cn, pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    assert ckt_lib.find(cn)
    return ckt_lib.find(cn)

def ele(ckt, name):
    return ckt.parent.find(ckt.get_element(name).model).elements[0]

@pytest.fixture
def path(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / (cn + ".sp")
    return test_path, pdk_path, config_path


@pytest.mark.parametrize("cn", ["intel_circuit"])
def test_sizing(ckt):
    assert ele(ckt, "X_XMP6").parameters["STACK"] == "2"
    assert ele(ckt, "X_XMP6").parameters["M"] == "4"
    assert ele(ckt, "X_XMP6").model == "PHVT"


@pytest.mark.parametrize("cn", ["intel_circuit1"])
def test_sizing1(ckt):
    assert ele(ckt, "X_XMP6").parameters["STACK"] == "6"
    assert ele(ckt, "X_XMP6").parameters["M"] == "4"
    assert ele(ckt, "X_XMP6").model == "PHVT"


@pytest.mark.parametrize("cn", ["intel_circuit2"])
def test_sizing2(ckt):
    assert {ele.name for ele in ckt.elements} == {'X_MN3_MN4', 'X_XI2', 'X_MN1', 'X_XI0', 'X_XI3_XI4', 'X_MN2', 'X_XI1'}
    assert ele(ckt, "X_XI0").parameters == {
        'W': '1.8E-07', 'L': '1', 'NFIN': '1', 'NF': '1', 'M': '4', 'PARALLEL': '1', 'STACK': '3'}
    assert ele(ckt, "X_XI0").model == "P"
    assert len(ckt.elements) == 7
    assert ele(ckt, "X_XI2")
    assert ele(ckt, "X_XI2").parameters["STACK"] == "2"
    assert ele(ckt, "X_XI2").parameters["M"] == "4"
    assert ele(ckt, "X_XI2").model == "PSVT"
    assert ckt.get_element("X_XI3_XI4")
    assert ckt.get_element("X_MN3_MN4")


@pytest.mark.parametrize("cn", ["intel_circuit3"])
def test_sizing3(ckt):
    assert ckt.elements[3]
    assert len(ckt.elements) == 5, f"{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element("X_MN2_MN3")
    assert ckt.parent.find("DP_NMOS_B_77995687"), f"Check hash is consistent? {[subckt.name for subckt in ckt.parent if 'DP_NMOS_B' in subckt.name]}"
    assert ckt.parent.find("DP_NMOS_B_77995687").elements[0].parameters["W"] == "3.6E-07"
    assert ele(ckt, "X_XI1").parameters["STACK"] == "3"
    assert ele(ckt, "X_XI1").model == "PSVT"


@pytest.mark.parametrize("cn", ["intel_circuit4"])
def test_sizing4(ckt):
    assert len(ckt.elements) == 5
    eles = set([ele.name for ele in ckt.elements])
    assert eles == {"X_XMP11_XMP12_XMP13", 'X_XMN0_XMP0', 'X_XMN1_XMP1', 'X_XMP3', 'X_XMN3'}
    assert len({v.name for v in ckt.parent if isinstance(v, SubCircuit) and 'INV_B' in v.name}) == 2
    assert len({v.name for v in ckt.parent if isinstance(v, SubCircuit) and 'CMB_PMOS' in v.name}) == 1
