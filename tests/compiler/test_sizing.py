import pathlib
import pytest
from align.compiler.compiler import compiler_input, compiler_output
from align.schema import SubCircuit


@pytest.fixture
def ckt(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / (cn + ".sp")
    ckt_library = compiler_input(test_path, cn, pdk_path, config_path)
    assert ckt_library.find(cn)
    return ckt_library.find(cn)


@pytest.fixture
def path(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / (cn + ".sp")
    return test_path, pdk_path, config_path


@pytest.mark.parametrize("cn", ["intel_circuit"])
def test_sizing(ckt):
    assert ckt.get_element('XMP6').parameters['STACK']=='2'
    assert ckt.get_element('XMP6').parameters['M']=='4'
    assert ckt.get_element('XMP6').model== 'PHVT'

@pytest.mark.parametrize("cn", ["intel_circuit1"])
def test_sizing1(ckt):
    assert ckt.get_element('XMP6').parameters['STACK']=='6'
    assert ckt.get_element('XMP6').parameters['M']=='4'
    assert ckt.get_element('XMP6').model== 'PHVT'


@pytest.mark.parametrize("cn", ["intel_circuit2"])
def test_sizing2(ckt):
    assert ckt.get_element('XI0').parameters['STACK']=='3'
    assert ckt.get_element('XI0').parameters['M']=='4'
    assert ckt.get_element('XI0').model== 'P'
    assert len(ckt.elements)==7
    assert ckt.get_element('XI2')
    assert ckt.get_element('XI2').parameters['STACK']=='2'
    assert ckt.get_element('XI2').parameters['M']=='4'
    assert ckt.get_element('XI2').model== 'PSVT'
    assert ckt.get_element('X_SCM_PMOS_B_XI3_XI4'), f"{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element('X_DP_NMOS_B_MN3_MN4')

@pytest.mark.parametrize('cn',['intel_circuit3'])
def test_sizing3(ckt):
    assert ckt.elements[3]
    assert len(ckt.elements) == 5, f"{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element('X_DP_NMOS_B_MN2_MN3')
    assert ckt.parent.find('DP_NMOS_B').elements[0].parameters['W']== '3.6E-07'
    assert ckt.get_element('XI1').parameters['STACK'] == '3'
    assert ckt.get_element('XI1').model == 'PSVT'

@pytest.mark.parametrize("cn", ["intel_circuit4"])
def test_sizing4(ckt):
    assert len(ckt.elements) == 5
    assert ckt.get_element('X_CMB_PMOS_2_XMP11_XMP12_XMP13'), f"{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element('X_INV_B_I1_XMN0_XMP0'), f"{[ele.name for ele in ckt.elements]}"
    assert len([v for v in ckt.parent if isinstance(v, SubCircuit)]) == 5
