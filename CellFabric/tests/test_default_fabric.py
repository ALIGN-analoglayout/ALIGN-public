from cell_fabric import DefaultCanvas, Pdk

import pytest
import fabric_default
import json
import itertools

@pytest.fixture
def setup():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)
    for (i,nm) in itertools.chain( itertools.product( [0,2,4], ['a']), itertools.product( [1,3,5], ['b'])):
        c.addWire( c.m1, nm, None, i, (0,1), (4,-1)) 
    return c

def test_via_postprocessor(setup):
    c = setup
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +b======+=======*
                    b
+a======+=======+   |
                    |
    +b======+=======/
""", xpitch=1, ypitch=1)

    # TODO: Figure out why this is failing
    # data = c.gen_data()

def test_fabric_default():
    unit_cap = 10

    fin_u1 = 8
    x_cells = 2
    y_cells = 1

    gate_u = 2
    if fin_u1%2 != 0:
        fin_u = fin_u1 + 1
    else:
        fin_u = fin_u1 

    uc = fabric_default.UnitCell( gate_u, fin_u, fin_u1)

    for (x,y) in itertools.product( range(x_cells), range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, gate_u)

    data = uc.gen_data()

    fn = "tests/__json_default_fabric_nmos"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)
        assert data['bbox'] == data_golden['bbox']
#        assert data == data_golden
        for (x,y) in zip( data['terminals'], data_golden['terminals']):
            x['netName'] = '_'
            y['netName'] = '_'
            x['pin'] = '_'
            y['pin'] = '_'
            assert x == y

