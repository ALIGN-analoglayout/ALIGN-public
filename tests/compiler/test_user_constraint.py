import pathlib
import pytest
import json

from align.compiler.compiler import compiler, compiler_output
from align.schema.checker import Z3Checker, CheckerError

@pytest.mark.parametrize('dir_name', ['high_speed_comparator_orderblock', \
    'high_speed_comparator_symmblock', 'high_speed_comparator_portlocation', 'high_speed_comparator_multiconnection', \
        'high_speed_comparator_align', 'high_speed_comparator_symmnet'])
def test_group_block_hsc(dir_name):
    circuit_name = 'high_speed_comparator'
    test_path = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_circuits' / dir_name / (circuit_name + '.sp')
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    updated_ckt = compiler(test_path, circuit_name, pdk_dir)
    assert 'DP_NMOS_B' in updated_ckt.keys()
    assert 'CCP_S_NMOS_B' in updated_ckt.keys()
    assert 'CCP_PMOS' in updated_ckt.keys()
    assert 'DP_NMOS_B' in updated_ckt.keys()
    assert 'INV' in updated_ckt.keys()
    assert 'dp' in updated_ckt.keys()
    assert 'ccn' in updated_ckt.keys()
    assert 'ccp' in updated_ckt.keys()
    assert 'inv_p' in updated_ckt.keys()
    assert 'inv_n' in updated_ckt.keys()
    out_path = pathlib.Path(__file__).resolve().parent
    result_path = out_path / 'Results'/ dir_name
    pdk_path = pathlib.Path(__file__).parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    compiler_output(test_path, updated_ckt, 'high_speed_comparator', result_path, pdk_path)
    gen_const_path = result_path / 'high_speed_comparator.verilog.json'
    gold_const_path = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_results' / (dir_name + '.const.json')
    with open(gen_const_path, "r") as const_fp:
        gen_const = next(x for x in json.load(const_fp)['modules'] if x['name'] == 'high_speed_comparator')["constraints"]
        gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const


@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
@pytest.mark.parametrize('dir_name', ['high_speed_comparator_broken'])
def test_constraint_checking(dir_name):
    circuit_name = 'high_speed_comparator'
    test_path = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_circuits' / dir_name / (circuit_name + '.sp')
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    with pytest.raises(CheckerError):
        updated_ckt = compiler(test_path, circuit_name, pdk_dir)

def test_scf():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    test_path = mydir.parent.parent / 'files' / 'test_circuits' / 'switched_capacitor_filter' / 'switched_capacitor_filter.sp'
    gen_const_path = mydir.parent / 'Results' / 'switched_capacitor_filter.verilog.json'
    gold_const_path = mydir.parent.parent / 'files' / 'test_results' / 'switched_capacitor_filter.const.json'

    updated_ckt = compiler(test_path, "switched_capacitor_filter", pdk_path)
    assert 'switched_capacitor_filter' in updated_ckt
    out_path = pathlib.Path(__file__).resolve().parent
    result_path = out_path / 'Results'/ 'switched_capacitor_filter'
    pdk_path = pathlib.Path(__file__).parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    compiler_output(test_path, updated_ckt, 'switched_capacitor_filter', result_path, pdk_path)
    gen_const_path = result_path / 'switched_capacitor_filter.verilog.json'
    gold_const_path = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_results' / 'switched_capacitor_filter.const.json'
    with open(gen_const_path, "r") as const_fp:
        gen_const = next(x for x in json.load(const_fp)['modules'] if x['name'] == 'switched_capacitor_filter')["constraints"]
        gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const
