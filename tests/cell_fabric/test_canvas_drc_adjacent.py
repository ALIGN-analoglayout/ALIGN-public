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

    m2['AdjacentAttacker'] = 1

    assert 'Width' in m2

    dy = m2['Width']//2
    py = m2['Pitch']

    c.terminals = [
        {'layer': 'M2', 'netName': 'x', 'rect': [   0, 0*py-dy, 200, 0*py+dy], "netType": "drawing"},
        {'layer': 'M2', 'netName': 'y', 'rect': [ 200, 1*py-dy, 400, 1*py+dy], "netType": "drawing"}
    ]

    return c

def test_adjacent_ok(setup):
    c = setup
    c.gen_data()
    assert c.drc.num_errors == 0

def test_adjacent_bad(setup):
    c = setup
    c.terminals[1]['rect'][0] += 1
    c.terminals[1]['rect'][2] += 1
    c.gen_data()
    assert c.drc.num_errors == 1

def test_adjacent_ok2(setup):
    c = setup
    c.terminals[1]['rect'][0] += 2
    c.terminals[1]['rect'][2] += 2
    c.gen_data()
    assert c.drc.num_errors == 0
