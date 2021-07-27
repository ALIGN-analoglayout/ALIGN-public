import pytest
import pathlib

from align.cell_fabric import Canvas, Pdk, Wire, Via

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="V1", h_clg=None, v_clg=None))

    m1 = p['M1']
    v1 = p['V1']
    m2 = p['M2']

    assert 'Width' in m1
    assert 'Width' in m2
    assert 'VencA_L' in v1
    assert 'VencA_H' in v1
    assert 'VencP_L' in v1
    assert 'VencP_H' in v1

    assert 'WidthX' in v1
    assert 'WidthY' in v1

    assert 'MinL' in m1
    assert 'MinL' in m2

    assert m1['MinL'] <= 200
    assert m2['MinL'] <= 200

    def cr( x, y):
        assert x%2 == 0
        assert y%2 == 0
        return [ -x//2, -y//2, x//2, y//2]

    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': cr( m1['Width'], v1['WidthY']+2*v1['VencA_L']), "netType": "drawing"},
                   {'layer': 'M2', 'netName': 'x', 'rect': cr( v1['WidthX']+2*v1['VencA_H'], m2['Width']), "netType": "drawing"},
                   {'layer': 'V1', 'netName': 'x', 'rect': cr( v1['WidthX'], v1['WidthY']), "netType": "drawing"}]

    return c

def test_enclosure_ok(setup):
    c = setup
    c.terminals[0]['rect'][1] -= 200
    c.terminals[1]['rect'][0] -= 200
    c.gen_data()
    assert c.drc.num_errors == 0

def test_enclosure_fail_right(setup):
    c = setup
    c.terminals[0]['rect'][1] -= 200
    c.terminals[1]['rect'][0] -= 200
    c.terminals[1]['rect'][2] -= 1
    c.gen_data()
    assert c.drc.num_errors == 1

def test_enclosure_fail_right_top(setup):
    c = setup
    c.terminals[0]['rect'][1] -= 200
    c.terminals[1]['rect'][0] -= 200
    c.terminals[1]['rect'][2] -= 1
    c.terminals[0]['rect'][3] -= 1
    c.gen_data()
    assert c.drc.num_errors == 2

def test_enclosure_fail_left(setup):
    c = setup
    c.terminals[0]['rect'][3] += 200
    c.terminals[1]['rect'][2] += 200
    c.terminals[1]['rect'][0] += 1
    c.gen_data()
    assert c.drc.num_errors == 1

def test_enclosure_fail_bottom(setup):
    c = setup
    c.terminals[0]['rect'][3] += 200
    c.terminals[1]['rect'][2] += 200
    c.terminals[0]['rect'][1] += 1
    c.gen_data()
    assert c.drc.num_errors == 1
