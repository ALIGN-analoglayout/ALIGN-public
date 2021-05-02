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
    library.append(subckt)
    for instance in [
        'mn0', 'mn1', 'mn2', 'mn3', 'mn4', 
        'mp5', 'mp6', 'mp7', 'mp8', 'mp9', 
        'mp10', 'mp11', 'mn13', 'mp12', 'mn14',
        'mn1_mn2', 'mn3_mn4', 'mp5_mp6', 'mp11_mn13', 'mp12_mn14']:
        with types.set_context(subckt.elements):
            subckt.elements.append(
                Instance(
                    name=instance,
                    model='nmos',
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
    assert gold_const == gen_const

