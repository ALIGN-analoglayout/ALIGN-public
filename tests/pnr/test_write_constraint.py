import pathlib
import pytest
import json

from align.pnr.write_constraint import PnRConstraintWriter
from align.schema import constraint

@pytest.mark.parametrize('results_file', 
    (pathlib.Path(__file__).parent.parent / 'files' / 'test_results').glob('*.pnr.const.json'),
    ids=lambda x: pathlib.Path(pathlib.Path(x.stem).stem).stem)
def test_group_block_hsc(results_file):
    name = pathlib.Path(pathlib.Path(results_file.stem).stem).stem
    constraint_file = pathlib.Path(__file__).parent.parent / 'files' / 'test_results' / (name + '.const.json')
    assert constraint_file.is_file()
    tmp_dir = pathlib.Path(__file__).parent.parent / 'tmp'
    tmp_dir.mkdir(exist_ok=True)
    tmp_file = tmp_dir / (name + '.pnr.const.json')
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

