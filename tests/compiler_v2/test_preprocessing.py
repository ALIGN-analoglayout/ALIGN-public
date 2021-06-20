import pathlib
import pytest
from align.compiler.compiler import compiler, compiler_output

@pytest.fixture
def primitives(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent.parent / 'files' / 'test_circuits' / (cn+'.sp')
    updated_ckt = compiler(test_path, cn,pdk_path )
    assert cn in updated_ckt
    return compiler_output(test_path, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )

@pytest.fixture
def path(cn):
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent.parent / 'files' / 'test_circuits' / (cn+'.sp')
    return test_path, pdk_path
    
@pytest.mark.parametrize('cn',['intel_circuit'])
def test_sizing(primitives):
    assert 'Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['stack']==2
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['vt_type']=='HVT'
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['parameters']['m']==4

@pytest.mark.parametrize('cn',['intel_circuit1'])
def test_sizing1(primitives):
    assert 'DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT' in primitives.keys()
    assert primitives['DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT']['stack']==6
    assert primitives['DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT']['vt_type']=='HVT'

@pytest.mark.parametrize('cn',['intel_circuit2'])
def test_sizing2(primitives):
    assert 'SCM_PMOS_B_nfin4_nf1_m3_n12_X1_Y1_ST3' in primitives.keys()
    assert 'DP_NMOS_B_nfin8_nf2_m5_n12_X7_Y1_HVT' in primitives.keys()
    assert 'Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3']['stack']==3
    assert primitives['Switch_PMOS_B_nfin6_nf4_m3_n12_X3_Y2_LVT']['vt_type']=='LVT'

@pytest.mark.parametrize('cn',['intel_circuit3'])
def test_sizing3(primitives):
    assert len(primitives) == 5
    assert 'DP_NMOS_B_nfin8_nf2_m5_n12_X7_Y1_HVT' in primitives.keys()
    assert 'Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3']['stack']==3
    assert primitives['Switch_PMOS_B_nfin6_nf4_m3_n12_X3_Y2_LVT']['vt_type']=='LVT'

@pytest.mark.parametrize('cn',['intel_circuit4'])
def test_sizing4(path):
    test_path, pdk_path = path
    updated_ckt = compiler(test_path, 'intel_circuit4',pdk_path )
    assert 'SCM_PMOS' in updated_ckt
    assert 'CMB_PMOS_2' in updated_ckt
    assert 'INV_B' in updated_ckt
    assert 'intel_circuit4' in updated_ckt
    primitives = compiler_output(test_path, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert  len(primitives) == 7
