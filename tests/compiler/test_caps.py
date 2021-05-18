import pathlib
import json

from align.compiler.compiler import compiler, compiler_output

def test_cap():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' 
    test_path = mydir.parent.parent / 'files' / 'test_circuits' / 'test_cap.sp'
    gen_const_path = mydir.parent / 'Results' / 'test_cap.verilog.json'
    gold_const_path = mydir.parent.parent / 'files' / 'test_results' / 'test_cap.const.json'

    updated_ckt = compiler(test_path, "test_cap", pdk_path)
    assert 'test_cap' in updated_ckt
    primitives = compiler_output(test_path, updated_ckt, 'test_cap', pathlib.Path(__file__).parent / 'Results', pdk_path)
    assert 'Cap_12f' in primitives.keys()
    with open(gen_const_path, "r") as const_fp:
        gen_const = next(x for x in json.load(const_fp)['modules'] if x['name'] == 'test_cap')["constraints"]
        gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const
