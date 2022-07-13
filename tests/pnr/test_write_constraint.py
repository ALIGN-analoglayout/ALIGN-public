from marshal import load
import pathlib
import pytest
import json

from align.pnr.write_constraint import PnRConstraintWriter
from align.schema import types, Instance, Library, SubCircuit, constraint, SpiceParser


@pytest.fixture
def mock_circuit():
    library = Library(loadbuiltins=True)
    n = library.find('nmos')
    assert n is not None
    with types.set_context(library):
        subckt = SubCircuit(
            name='high_speed_comparator',
            pins=['clk', 'vcc', 'vin', 'vip', 'von', 'vop', 'vss', 'vinn', 'vinp', 'voutn', 'voutp'])
        dummy_sub = SubCircuit(
            name='dummy',
            pins=['D', 'G', 'S', 'B'])
    library.append(subckt)
    library.append(dummy_sub)
    for instance in [
        'X_MN0', 'X_MN1', 'X_MN2', 'X_MN3', 'X_MN4', 'X_M12_M14', 'X_M3', 'X_M11', 'X_M5', 'X_M9', 'XI0', 'X_M4_M8',
        'X_MP5', 'X_MP6', 'X_MP7', 'X_MP8', 'X_MP9', 'X_C2', 'X_C3', 'X_C6', 'X_C5', 'X_C1', 'X_C0', 'X_C4', 'X_C7', 'X_M6_M7', 'X_C8', 'X_C9',
        'X_M10_M7', 'X_M12_M6',
        'X_MP10', 'X_MP11', 'X_MN13', 'X_MP12', 'X_MN14', 'X_MP7_MP8', 'X_MP8_MP9', 'X_M0_M14', 'X_MP10_MP9',
            'X_DP_MN1_MN2', 'X_CCN_MN3_MN4', 'X_CCP_MP5_MP6', 'X_INV_N_MP11_MN13', 'X_INV_P_MP12_MN14']:
        with types.set_context(subckt.elements):
                subckt.elements.append(
                    Instance(
                        name=instance,
                        model='dummy',
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
    with types.set_context(mock_circuit.constraints):
        mock_circuit.constraints.extend(constraints)
    with open(tmp_file, 'w') as outfile:
        json.dump(PnRConstraintWriter().map_valid_const(mock_circuit.constraints, mock_circuit), outfile, indent=4)
    with open(tmp_file, "r") as const_fp:
        gen_const = json.load(const_fp)["constraints"]
        gen_const.sort(key=lambda item: item.get("const_name"))
    with open(results_file, "r") as const_fp:
        gold_const = json.load(const_fp)["constraints"]
        gold_const.sort(key=lambda item: item.get("const_name"))
    assert gold_const == gen_const
