import pathlib

from align.compiler.compiler import compiler, compiler_output

def test_sizing():
    test_path=pathlib.Path(__file__).resolve().parent / 'test3_sizing.sp'
    updated_ckt,library = compiler(test_path, "sizing",0 )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'DP_NMOS' in all_subckt_list
    assert 'sizing' in all_subckt_list

    return(updated_ckt,library)
def test_sizing_output():
    updated_ckt,library = test_sizing()
    # Every example should contain a setup file
    test_path=pathlib.Path(__file__).resolve().parent / 'test3_sizing.sp'
    compiler_output(test_path, library, updated_ckt, 'sizing', pathlib.Path(__file__).parent / 'Results', 'FinFET14nm_Mock_PDK' )
