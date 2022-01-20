from align.schema.types import set_context
import pathlib
import pytest
from align.schema.parser import SpiceParser
from align.schema import constraint
from align.compiler.read_library import read_lib, read_models, order_lib
from tests.schema.test_graph import primitives


@pytest.fixture
def library():
    parser = SpiceParser()
    align_home = pathlib.Path(__file__).resolve().parent.parent / "files"
    basic_lib_path = align_home / "basic_template.sp"
    with open(basic_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    user_lib_path = align_home / "user_template.sp"
    with open(user_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    return parser.library


def test_basic_lib(library):
    assert len(library.find("DP_PMOS_B").elements) == 2
    assert len(library.find("CASCODED_CMC_PMOS").elements) == 4
    assert len(library.find("INV_B").elements) == 2
    assert len(library) == 54


def test_constraint(library):
    assert len(library.find("DP_PMOS_B").constraints) == 3
    dp_const = library.find("DP_PMOS_B").constraints
    with set_context(dp_const):
        x = constraint.SymmetricBlocks(direction="V", pairs=[["M0", "M1"]])
    assert x in dp_const
    assert dp_const[0].constraint == "symmetric_blocks"
    assert dp_const[0].pairs == [["M0", "M1"]]


def test_default_models():
    mydir = pathlib.Path(__file__).resolve().parent
    pdk_dir = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    ckt_parser = read_models(pdk_dir)
    assert len(ckt_parser.library) == 35


def test_default_template_lib():
    mydir = pathlib.Path(__file__).resolve().parent
    pdk_dir = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    library = read_lib(pdk_dir)
    assert len(library) == 104
    primitives_list = order_lib(library)
    assert len(primitives_list) == 69
    assert primitives_list[56].name == "DCL_PMOS_S"
    assert primitives_list[2].name == "SCM_PMOS_RC"
    assert primitives_list[14].name == "DP_PAIR_PMOS"
