import pytest
import pathlib

from align.cell_fabric import Canvas, Pdk, Wire

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))

    m2 = p['M2']

    assert 'Width' in m2
    assert m2['Width'] % 2 == 0

    dy0 = m2['Width']//2
    dy1 = dy0 + 4

    c.terminals = [
        {'layer': 'M2', 'netName': 'x', 'rect': [    0, -dy0,  200, dy0]},
        {'layer': 'M2', 'netName': 'x', 'rect': [  200, -dy0,  400, dy0]},
        {'layer': 'M2', 'netName': 'y', 'rect': [ 1000, -dy1, 1200, dy1]}
    ]

    return c

@pytest.fixture
def setup2():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))

    m2 = p['M2']

    assert 'Width' in m2
    assert m2['Width'] % 2 == 0

    dy0 = m2['Width']//2
    dy1 = dy0 + 4

    c.terminals = [
        {'layer': 'M2', 'netName': 'y', 'rect': [ -1000, -dy1, -800, dy1]},
        {'layer': 'M2', 'netName': 'x', 'rect': [     0, -dy0,  200, dy0]},
        {'layer': 'M2', 'netName': 'x', 'rect': [   200, -dy0,  400, dy0]}
    ]

    return c

def test_merged_ok(setup):
    c = setup

    assert len(c.terminals) == 3

    c.gen_data()

    assert c.drc.num_errors == 0
    assert len(c.terminals) == 2

def test_merged_ok2(setup2):
    c = setup2

    assert len(c.terminals) == 3

    c.gen_data()

    assert c.drc.num_errors == 0
    assert len(c.terminals) == 2


