import pathlib

from align.compiler.compiler import compiler, compiler_output

def test_compiler():
    test_path=pathlib.Path(__file__).resolve().parent / 'test_circuits' / 'ota' / 'ota.sp'
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'

    updated_ckt,library = compiler(test_path, "ota",pdk_dir )
    assert 'CMC_PMOS' in updated_ckt
    assert 'SCM_NMOS' in updated_ckt
    assert 'CMC_S_NMOS_B' in updated_ckt
    assert 'DP_NMOS_B' in updated_ckt
    assert 'ota' in updated_ckt

    return(updated_ckt,library)

def test_compiler_output():
    updated_ckt,library=test_compiler()
    # Every example should contain a setup file
    test_path=pathlib.Path(__file__).resolve().parent / 'ota.sp'
    compiler_output(test_path, library, updated_ckt, 'ota', pathlib.Path(__file__).parent / 'Results', pathlib.Path(__file__).parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' )
