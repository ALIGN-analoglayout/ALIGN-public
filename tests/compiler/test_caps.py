import pathlib
import json

from align.compiler.compiler import compiler, compiler_output

def test_cap():
    mydir = pathlib.Path(__file__).resolve()
    test_path = mydir.parent / 'test_circuits' / 'test_cap.sp'
    gen_const_path = mydir.parent / 'Results' / 'test_cap.const.json'
    gold_const_path = mydir.parent / 'test_results' / 'test_cap.const.json'

    updated_ckt,library = compiler(test_path, "test_cap",0 )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'test_cap' in all_subckt_list
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    primitives = compiler_output(test_path, library, updated_ckt, 'test_cap', pathlib.Path(__file__).parent / 'Results', pdk_path )
    assert 'Cap_12f' in primitives.keys()
    with open(gen_const_path, "r") as const_fp:
        gen_const = json.load(const_fp)
    with open(gold_const_path, "r") as const_fp:
            gold_const = json.load(const_fp)
    assert gold_const == gen_const
