import pytest
import pathlib

from align.cell_fabric import Canvas, Pdk, Wire, Via

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Wire( nm='m3', layer='M3', direction='v', clg=None, spg=None))
    c.addGen( Via( nm="v2", layer="V2", h_clg=None, v_clg=None))

    m2 = p['M2']
    v2 = p['V2']
    m3 = p['M3']

    assert 'Width' in m2
    assert 'Width' in m3
    assert 'VencA_L' in v2
    assert 'VencA_H' in v2
    assert 'VencP_L' in v2
    assert 'VencP_H' in v2

    assert 'WidthX' in v2
    assert 'WidthY' in v2

    assert 'MinL' in m2
    assert 'MinL' in m3

    assert m2['MinL'] <= 210
    assert m3['MinL'] <= 210

    def cr( x, y):
        assert x%2 == 0
        assert y%2 == 0
        return [ -x//2, -y//2, x//2, y//2]

    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': cr( v2['WidthX']+2*v2['VencA_L'], m2['Width']), "netType": "drawing"},
                   {'layer': 'M3', 'netName': 'x', 'rect': cr( m3['Width'], v2['WidthY']+2*v2['VencA_H']), "netType": "drawing"},
                   {'layer': 'V2', 'netName': 'x', 'rect': cr( v2['WidthX'], v2['WidthY']), "netType": "drawing"}]

    return c

def test_enclosure_ok(setup):
    c = setup
    c.terminals[1]['rect'][1] -= 210
    c.terminals[0]['rect'][0] -= 210
    c.gen_data()
    assert c.drc.num_errors == 0

def test_enclosure_fail_right(setup):
    c = setup
    c.terminals[1]['rect'][1] -= 210
    c.terminals[0]['rect'][0] -= 210
    c.terminals[0]['rect'][2] -= 1
    c.gen_data()
    assert c.drc.num_errors == 1

def test_enclosure_fail_right_top(setup):
    c = setup
    c.terminals[1]['rect'][1] -= 210
    c.terminals[0]['rect'][0] -= 210
    c.terminals[0]['rect'][2] -= 1
    c.terminals[1]['rect'][3] -= 1
    c.gen_data()
    assert c.drc.num_errors == 2

def test_enclosure_fail_left(setup):
    c = setup
    c.terminals[1]['rect'][3] += 210
    c.terminals[0]['rect'][2] += 210
    c.terminals[0]['rect'][0] += 1
    c.gen_data()
    assert c.drc.num_errors == 1

def test_enclosure_fail_bottom(setup):
    c = setup
    c.terminals[1]['rect'][3] += 210
    c.terminals[0]['rect'][2] += 210
    c.terminals[1]['rect'][1] += 1
    c.gen_data()
    assert c.drc.num_errors == 1
