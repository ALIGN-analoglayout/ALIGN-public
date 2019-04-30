import networkx as nx

from basic_element import BasicElement, _parse_inst

def test_blank():
    be = _parse_inst("")    
    assert be is None

def test_r():
    be = _parse_inst("ra 1 0 10k")

def test_v_source():
    be = _parse_inst("v0 1 0 1.0")

def test_e_source():
    be = _parse_inst("e0 1 0 2 0 1.0")

def test_i_source():
    be = _parse_inst("i0 1 0 1.0")

def test_pmos_source():
    be = _parse_inst("m0 3 2 1 1 p")
