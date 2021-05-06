import pytest
import pathlib

from align.cell_fabric import Canvas, Pdk, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="V1", h_clg=None, v_clg=None))
    return c

def test_min_length_pass_v(setup):
    c = setup
    # L(300) > MinL(180)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]}]
    c.gen_data() 
    assert c.drc.num_errors == 0

def test_min_length_pass_h(setup):
    c = setup
    # L(300) > MinL(200)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 300, 100]}]
    c.gen_data()
    assert c.drc.num_errors == 0

def test_min_length_fail_v(setup):
    c = setup
    # L(175) < MinL(180)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 175]}]
    c.gen_data()
    print(c.drc.errors) 
    assert c.drc.num_errors == 1

def test_min_length_fail_h(setup):
    c = setup
    # L(190) < MinL(200)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 190, 100]}]
    c.gen_data()
    assert c.drc.num_errors == 1

def test_min_spacing_pass_v(setup):
    c = setup
    # space(50) > End-To-End(48)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]},
                   {'layer': 'M1', 'netName': 'x', 'rect': [0, 350, 100, 650]}]
    c.gen_data()
    assert c.drc.num_errors == 0

def test_min_spacing_pass_h(setup):
    c = setup
    # space(50) > End-To-End(48)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [  0, -50, 200, 50]},
                   {'layer': 'M2', 'netName': 'x', 'rect': [250, -50, 600, 50]}]
    c.gen_data()
    assert c.drc.num_errors == 0

def test_min_spacing_fail_v(setup):
    c = setup
    # space(40) < End-To-End(48)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]},
                   {'layer': 'M1', 'netName': 'x', 'rect': [0, 340, 100, 640]}]
    c.gen_data()
    assert c.drc.num_errors == 1

def test_min_spacing_fail_h(setup):
    c = setup
    # space(40) < End-To-End(48)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [  0, -50, 200, 50]},
                   {'layer': 'M2', 'netName': 'x', 'rect': [240, -50, 600, 50]}]
    c.gen_data()
    assert c.drc.num_errors == 1

def test_grid():
    from align.pdk.finfet.canvas import CanvasPDK
    c = CanvasPDK()
    # Below yields [780, 700, 1380, 5600]
    # c.addWire(c.m1, 'a', None, 1, (1, -1), (6, 1))
    c.terminals.append({'layer': 'M1', 'netName': 'a', 'rect': [780, 700, 1390, 5600]})
    c.gen_data(run_drc=True)
    assert c.drc.num_errors == 1
