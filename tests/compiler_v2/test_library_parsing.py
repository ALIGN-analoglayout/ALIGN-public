import pathlib

from align.schema.parser import SpiceParser


def test_basic_lib():

    parser = SpiceParser()
    align_home = pathlib.Path(__file__).resolve().parent.parent.parent / 'align'
    model_statemenets = align_home / 'config' / 'model.txt'
    with open(model_statemenets) as f:
        lines = f.read()
    parser.parse(lines)
    basic_lib_path = align_home / 'config' / 'basic_template_copy.sp'
    with open(basic_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    assert len(parser.library) == 76
    assert 'DCL_PMOS' in parser.library
    assert 'LS_S_NMOS_B' in parser.library
    assert len(parser.library['DP_PMOS_B'].elements) == 2
    assert len(parser.library['CASCODED_CMC_PMOS'].elements) == 4

    user_lib_path = align_home / 'config' / 'user_template_copy.sp'
    with open(user_lib_path) as f:
        lines = f.read()
    parser.parse(lines)
    assert len(parser.library) == 100

