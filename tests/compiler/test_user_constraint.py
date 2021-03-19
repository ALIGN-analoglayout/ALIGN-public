import pathlib
import pytest
import json

from align.compiler.compiler import compiler, compiler_output

@pytest.fixture
def test_compiler_hsc(dir_name):
    circuit_name = 'high_speed_comparator'
    test_path=pathlib.Path(__file__).resolve().parent / 'test_circuits' / dir_name / (circuit_name+'.sp')
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    updated_ckt, library = compiler(test_path, circuit_name, pdk_dir)
    assert 'DP_NMOS_B' in updated_ckt
    assert 'CCP_S_NMOS_B' in updated_ckt
    assert 'CCP_PMOS' in updated_ckt
    assert 'DP_NMOS_B' in updated_ckt
    assert 'INV' in updated_ckt
    return (updated_ckt, library, dir_name)

@pytest.mark.parametrize('dir_name', ['high_speed_comparator_orderblock', \
    'high_speed_comparator_symmblock', 'high_speed_comparator_portlocation', 'high_speed_comparator_multiconnection', \
        'high_speed_comparator_align'])
def test_group_block_hsc(test_compiler_hsc):
    updated_ckt, library, dir_name = test_compiler_hsc
    assert 'dp' in updated_ckt
    assert 'ccn' in updated_ckt
    assert 'ccp' in updated_ckt
    assert 'inv_p' in updated_ckt
    assert 'inv_n' in updated_ckt
    
    test_path = pathlib.Path(__file__).resolve().parent
    result_path = test_path / 'Results'/ dir_name
    pdk_path = pathlib.Path(__file__).parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    compiler_output(test_path, library, updated_ckt, 'ota', result_path, pdk_path)
    gen_const_path = result_path / 'high_speed_comparator.const.json'
    gold_const_path = test_path / 'test_results' / (dir_name + '.const.json')
    with open(gen_const_path, "r") as const_fp:
        gen_const = json.load(const_fp)
    with open(gold_const_path, "r") as const_fp:
            gold_const = json.load(const_fp)
    assert gold_const == gen_const
