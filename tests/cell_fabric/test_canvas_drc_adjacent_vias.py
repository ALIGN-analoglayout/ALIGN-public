
import pytest
import json

from align.cell_fabric import Pdk, Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

@pytest.fixture
def setup():
    p = Pdk()
    p.pdk['M2'] = { 'Direction': 'H', 'Width': 60, 'Pitch': 100, 'MinL': 10, 'EndToEnd': 10}
    p.pdk['M3'] = { 'Direction': 'V', 'Width': 50, 'Pitch': 100, 'MinL': 10, 'EndToEnd': 10}

#
# Adjacent via violation
# *****    *****
#   ^        ^
# WidthX + SpaceX > Pitch(X)
#
# Both okay below
#
    p.pdk['V2'] = { 'Stack': ['M2', 'M3'],
                'WidthX': 50,
                'WidthY': 60,
                'SpaceX': 50,
                'SpaceY': 40,
                'VencA_L': 0,
                'VencA_H': 0,
                'VencP_L': 0,
                'VencP_H': 0
    }

    c = Canvas(p)

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=p['M2']['Width'], pitch=p['M2']['Pitch']),
                         spg=EnclosureGrid( pitch=p['M3']['Pitch'], stoppoint=p['M3']['Pitch']//2)))

    m3 = c.addGen( Wire( nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid( width=p['M3']['Width'], pitch=p['M3']['Pitch']),
                         spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['M2']['Pitch']//2)))


    v2 = c.addGen( Via( nm='v2', layer='V2', h_clg=m2.clg, v_clg=m3.clg))

    n = 40
    gridlines = list(range(n))

    for i in gridlines:
        c.addWire( m3, 'a', i, (0,1), (n+1,-1)) 

    for j in gridlines:
        c.addWireAndViaSet( 'a', m2, v2, j+1, gridlines)

    return c,n


def test_adjacent_ok(setup):
    c,_ = setup
    data = c.gen_data(run_pex=False)

    if False:
        with open( "__json_hack", "wt") as fp:
            json.dump( data, fp=fp, indent=2)

    assert c.drc.num_errors == 0

def test_adjacent_violate_x(setup):
    c,n = setup
    c.pdk['V2']['SpaceX'] += 1

    c.gen_data(run_pex=False)

    assert c.drc.num_errors == n*(n-1)

def test_adjacent_violate_y(setup):
    c,n = setup
    c.pdk['V2']['SpaceY'] += 1

    c.gen_data(run_pex=False)

    assert c.drc.num_errors == n*(n-1)

