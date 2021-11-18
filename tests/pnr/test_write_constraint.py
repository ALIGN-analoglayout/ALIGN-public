import pathlib
import pytest
import json

from align.pnr.write_constraint import PnRConstraintWriter
from align.schema import types, Instance, Library, SubCircuit, constraint, SpiceParser

@pytest.fixture
def mock_circuit():
    library = Library()
    n = library.find('nmos')
    assert n is not None
    with types.set_context(library):
        subckt = SubCircuit(
                name = 'high_speed_comparator',
                pins = ['clk', 'vcc', 'vin', 'vip', 'von', 'vop', 'vss'])
        dummy_sub = SubCircuit(
                name = 'dummy',
                pins = ['D', 'G', 'S', 'B'])
    library.append(subckt)
    library.append(dummy_sub)
    for instance in [
        'MN0', 'MN1', 'MN2', 'MN3', 'MN4', 'X_CMC_S_NMOS_B_I1_M12_M14',
        'MP5', 'MP6', 'MP7', 'MP8', 'MP9', 'C2', 'C5', 'C1', 'X_CMC_S_NMOS_B_I1_M6_M7', 'C8', 'C9',
        'MP10', 'MP11', 'MN13', 'MP12', 'MN14', 'X_CMC_PMOS_MP10_MP7', 'X_CMC_PMOS_MP8_MP9',
        'X_DP_MN1_MN2', 'X_CCN_MN3_MN4', 'X_CCP_MP5_MP6', 'X_INV_N_MP11_MN13', 'X_INV_P_MP12_MN14']:
        with types.set_context(subckt.elements):
            if instance.startswith('M'):
                subckt.elements.append(
                    Instance(
                        name=instance,
                        model='nmos',
                        generator='',
                        pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET11', 'B': 'NET13'})
                )
            elif instance.startswith('C'):
                subckt.elements.append(
                    Instance(
                        name=instance,
                        model='cap',
                        generator='',
                        pins={'PLUS': 'NET10', 'MINUS': 'NET12'})
                )
            else:
                subckt.elements.append(
                    Instance(
                        name=instance,
                        model='dummy',
                        generator='',
                        pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET11', 'B': 'NET13'})
                )

    return subckt

@pytest.mark.parametrize('results_file',
    (pathlib.Path(__file__).parent.parent / 'files' / 'test_results').glob('*.pnr.const.json'),
    ids=lambda x: pathlib.Path(pathlib.Path(x.stem).stem).stem)
def test_group_block_hsc(results_file, mock_circuit):
    name = pathlib.Path(pathlib.Path(results_file.stem).stem).stem
    constraint_file = pathlib.Path(__file__).parent.parent / 'files' / 'test_results' / (name + '.const.json')
    assert constraint_file.is_file()
    tmp_dir = pathlib.Path(__file__).parent.parent / 'tmp'
    tmp_dir.mkdir(exist_ok=True)
    tmp_file = tmp_dir / (name + '.pnr.const.json')
    with types.set_context(mock_circuit):
        constraints = constraint.ConstraintDB.parse_file(constraint_file)
    with open(tmp_file, 'w') as outfile:
        json.dump(PnRConstraintWriter().map_valid_const(constraints), outfile, indent=4)
    with open(tmp_file, "r") as const_fp:
        gen_const = json.load(const_fp)["constraints"]
        gen_const.sort(key=lambda item: item.get("const_name"))
    with open(results_file, "r") as const_fp:
        gold_const = json.load(const_fp)["constraints"]
        gold_const.sort(key=lambda item: item.get("const_name"))
    assert gold_const == gen_const, f'golden: {results_file} current: {tmp_file}'
