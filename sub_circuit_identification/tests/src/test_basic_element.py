from os.path import dirname, abspath, join
import sys

# Find code directory relative to our directory
THIS_DIR = dirname(__file__)
CODE_DIR = abspath(join(THIS_DIR, '../../', 'src'))
sys.path.append(CODE_DIR)
print(sys.path)
from basic_element import _parse_inst

def test_blank():
    be = _parse_inst("")
    assert be is None

def test_r():
    dev = _parse_inst("ra 1 0 10k")
    assert len(dev.items()) == 6
    assert dev['inst_type'] == "res"

def test_v_source():
    dev = _parse_inst("v0 1 0 1.0")
    assert len(dev.items()) == 6
    assert dev['inst_type'] == "v_source"

def test_e_source():
    dev = _parse_inst("e0 1 0 2 0 1.0")
    assert len(dev.items()) == 6

def test_i_source():
    dev = _parse_inst("i0 1 0 1.0")
    assert len(dev.items()) == 6

def test_nmos():
    dev = _parse_inst("m0 3 2 1 1 n nfin=1")
    assert len(dev.items()) == 6

def test_nmos1():
    dev = _parse_inst("m0 (3 2 1 1) n nfin=1")
    assert len(dev.items()) == 6

def test_nmos_err():
    _parse_inst("m0 3 2=4 1 1 n nfin=1")
    assert AttributeError

def test_pmos_param():
    dev = _parse_inst("m0 3 2 1 1 p nfin = 1")
    assert len(dev.items()) == 6

def test_subckt_param():
    dev = _parse_inst("xdp D G S nmos p=1")
    assert len(dev["values"].items()) == 1

def test_subckt_param_backslash():
    dev = _parse_inst('xdp D G S / nmos p=1')
    assert len(dev["values"].items()) == 1

def test_subckt_param_spaces():
    dev = _parse_inst("xdp D S G nmos p = 1")
    assert len(dev["values"].items()) == 1
