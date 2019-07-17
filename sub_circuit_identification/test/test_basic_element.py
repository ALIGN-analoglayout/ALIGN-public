
from src import _parse_inst

def test_blank():
    be = _parse_inst("")
    assert be is None

def test_r():
    dev = _parse_inst("ra 1 0 10k")
    assert len(dev.items()) == 5
    assert dev['inst_type'] == "res"

def test_v_source():
    dev = _parse_inst("v0 1 0 1.0")
    assert len(dev.items()) == 5
    assert dev['inst_type'] == "v_source"

def test_e_source():
    dev = _parse_inst("e0 1 0 2 0 1.0")
    assert len(dev.items()) == 5

def test_i_source():
    dev = _parse_inst("i0 1 0 1.0")
    assert len(dev.items()) == 5

def test_pmos():
    dev = _parse_inst("m0 3 2 1 1 p")
    assert len(dev.items()) == 5

def test_pmos_param():
    dev = _parse_inst("m0 3 2 1 1 p nfin = 1")
    assert len(dev.items()) == 5

def test_subckt_param():
    dev = _parse_inst("xdp D G S nmos p=1")
    assert len(dev["values"].items()) == 1

def test_subckt_param_backslash():
    dev = _parse_inst('xdp D G S / nmos p=1')
    assert len(dev["values"].items()) == 1

def test_wrong_name():
    dev = _parse_inst("m0=1 3 2 1 1 p")
    print("checking,",dev)
    assert dev == None

def test_subckt_param_spaces():
    dev = _parse_inst("xdp D S G nmos p = 1")
    assert len(dev["values"].items()) == 1
