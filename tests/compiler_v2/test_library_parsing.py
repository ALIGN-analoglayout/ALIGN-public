from align.schema.types import set_context
import pathlib
import pytest
from align.schema.parser import SpiceParser
from align.schema import constraint

@pytest.fixture
def library():
    parser = SpiceParser()
    align_home = pathlib.Path(__file__).resolve().parent.parent.parent / 'align'
    basic_lib_path = align_home / 'config' / 'basic_template.sp'
    with open(basic_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    user_lib_path = align_home / 'config' / 'user_template.sp'
    with open(user_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    return parser.library

def test_basic_lib(library):
    assert len(library.find('DP_PMOS_B').elements) == 2
    assert len(library.find('CASCODED_CMC_PMOS').elements) == 4
    assert len(library.find('INV_B').elements)==2
    assert len(library) == 54

def test_constraint(library):
    assert len(library.find('DP_PMOS_B').constraints)==1
    print(library.find('DP_PMOS_B').constraints)
    dp_const = library.find('DP_PMOS_B').constraints
    with set_context(dp_const):
        x=constraint.SymmetricBlocks(direction='V', pairs=[['M0', 'M1']])
    assert x in dp_const
    assert dp_const[0].constraint=='symmetric_blocks'
    assert dp_const[0].pairs == [['M0', 'M1']]
