import pathlib

from align.compiler.compiler import compiler, compiler_output

def test_sizing():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 

    test_path = mydir.parent / 'test_circuits' / 'intel_circuit.sp'
    updated_ckt,library = compiler(test_path, "intel_circuit",pdk_path )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'intel_circuit' in all_subckt_list
    primitives = compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert 'Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['stack']==2
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['vt_type']=='HVT'
    assert primitives['Switch_PMOS_B_nfin6_m4_n12_X2_Y1_ST2_HVT']['parameters']['m']==4

def test_sizing1():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent / 'test_circuits' / 'intel_circuit1.sp'
    updated_ckt,library = compiler(test_path, "intel_circuit1",pdk_path )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'intel_circuit1' in all_subckt_list
    primitives = compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert 'DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT' in primitives.keys()
    assert primitives['DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT']['stack']==6
    assert primitives['DCL_PMOS_B_nfin6_m4_n12_X2_Y1_ST6_HVT']['vt_type']=='HVT'

def test_sizing2():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent / 'test_circuits' / 'intel_circuit2.sp'
    updated_ckt,library = compiler(test_path, "intel_circuit2",pdk_path )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'DP_NMOS_B' in all_subckt_list
    assert 'SCM_PMOS_B' in all_subckt_list
    assert 'intel_circuit2' in all_subckt_list
    primitives = compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert 'Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3']['stack']==3
    assert primitives['Switch_PMOS_B_nfin6_nf4_m3_n12_X3_Y2_LVT']['vt_type']=='LVT'

def test_sizing3():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent / 'test_circuits' / 'intel_circuit3.sp'
    updated_ckt,library = compiler(test_path, "intel_circuit3",pdk_path )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'DP_NMOS_B' in all_subckt_list
    assert 'intel_circuit3' in all_subckt_list
    primitives = compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert  len(primitives) == 5
    assert 'Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3' in primitives.keys()
    assert primitives['Switch_PMOS_B_nfin4_nf1_m4_n12_X2_Y1_ST3']['stack']==3
    assert primitives['Switch_PMOS_B_nfin6_nf4_m3_n12_X3_Y2_LVT']['vt_type']=='LVT'

def test_sizing4():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent / 'test_circuits' / 'intel_circuit4.sp'
    updated_ckt,library = compiler(test_path, "intel_circuit4",pdk_path )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'SCM_PMOS' in all_subckt_list
    assert 'CMB_PMOS_2' in all_subckt_list
    assert 'INV_B' in all_subckt_list
    assert 'intel_circuit4' in all_subckt_list
    primitives = compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert  len(primitives) == 7
