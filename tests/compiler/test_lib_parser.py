import pathlib
import shutil
import textwrap

from align.schema.types import set_context
from align.schema.parser import SpiceParser
from align.schema import constraint
from align.compiler.read_library import read_lib, read_models, order_lib
from utils import get_test_id


def test_basic_lib():
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
    library = parser.library

    assert len(library.find("DP_PMOS_B").elements) == 2
    assert len(library.find("CASCODED_CMC_PMOS").elements) == 4
    assert len(library.find("INV_B").elements) == 2
    assert len(library) == 78

    assert len(library.find("DP_PMOS_B").constraints) == 4
    dp_const = library.find("DP_PMOS_B").constraints
    with set_context(dp_const):
        x = constraint.SymmetricBlocks(direction="V", pairs=[["M1", "M2"]])
    assert x in dp_const
    assert isinstance(dp_const[1], constraint.SymmetricBlocks)
    assert dp_const[1].pairs == [["M1", "M2"]]


def test_basic_models():
    mydir = pathlib.Path(__file__).resolve().parent
    name = f'ckt_{get_test_id()}'.upper()
    dummy_pdk_dir = mydir / name
    dummy_pdk_dir.mkdir(exist_ok=True)
    (dummy_pdk_dir / '__init__.py').touch()
    ckt_parser = read_models(dummy_pdk_dir)
    assert len(ckt_parser.library) == 5
    shutil.rmtree(dummy_pdk_dir)

def test_subckt_generator_dummy():
    mydir = pathlib.Path(__file__).resolve().parent
    name = f'ckt_{get_test_id()}'.upper()
    dummy_pdk_dir = mydir / name
    dummy_pdk_dir.mkdir(exist_ok=True)
    (dummy_pdk_dir / '__init__.py').touch()
    dummy_gen = textwrap.dedent(f"""\
    class dummy():
        pass
    """)
    with open(dummy_pdk_dir / f'dummy_gen.py', 'w') as fp:
        fp.write(dummy_gen)
    with open(dummy_pdk_dir / f'__init__.py', 'w') as fp:
        fp.write('from .dummy_gen import *')
    netlist = textwrap.dedent(f"""\
    .subckt dummy a o vccx vssx
    M0 o a vccx vccx pmos w=45e-9 m=1 nf=1
    .ends
    """)
    with open(dummy_pdk_dir / f'user_template.sp', 'w') as fp:
        fp.write(netlist)
    library = read_lib(dummy_pdk_dir)
    assert library.find('DUMMY')
    assert library.find('DUMMY').generator['name'] == 'DUMMY'
    shutil.rmtree(dummy_pdk_dir)


def test_default_models():
    mydir = pathlib.Path(__file__).resolve().parent
    pdk_dir = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    ckt_parser = read_models(pdk_dir)
    assert len(ckt_parser.library) == 35


def test_default_template_lib():
    mydir = pathlib.Path(__file__).resolve().parent
    pdk_dir = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    library = read_lib(pdk_dir)
    assert len(library) == 108
    primitives_list = order_lib(library)
    assert len(primitives_list) == 73
    assert primitives_list[56].name == "DCAP_PMOS"
    assert primitives_list[2].name == "SCM_PMOS_RC"
    assert primitives_list[14].name == "DP_PAIR_PMOS"
