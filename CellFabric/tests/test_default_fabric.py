from cell_fabric import DefaultCanvas, Pdk

import pytest
import fabric_CMC_NMOS_v1_default ### This is most updtaed cell fabric, therefore, replaced the fabric_default 
import json
import itertools

@pytest.fixture
def setup():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)
    for (i,nm) in itertools.chain( itertools.product( [0,2,4], ['a']), itertools.product( [1,3,5], ['b'])):
        c.addWire( c.m1, nm, None, i, (0,-1), (3,-1)) 
    return c

def test_v3(setup):
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)

    c.addWire( c.m3, "a", None, 1, (-2,1), (4,-1))
    c.addWire( c.m4, "a", None, 1, (-2,1), (4,-1))
    c.addVia( c.v3, None, None, 1, 1)
    data = c.gen_data()

    fn = "tests/__json_v3"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')


def test_v2(setup):
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)

    c.addWire( c.m2, "a", None, 1, (-2,1), (4,-1))
    c.addWire( c.m3, "a", None, 1, (-2,1), (4,-1))
    c.addVia( c.v2, None, None, 1, 1)
    data = c.gen_data()

    fn = "tests/__json_v2"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')



def test_beol_stack(setup):
    c = setup
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +b======+=======*
                    b
+a======+=======+   |
                    |
    +b======+=======/
""")

    c.asciiStickDiagram( c.v3, c.m4, c.v4, c.m5, """
            /=======+
            |
            |
            |
            /b======+
""")

    data = c.gen_data()

    fn = "tests/__json_default_fabric_beol_sticks"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data2 = json.load( fp)

        assert data == data2

def test_fabric_default():
    unit_cap = 10

    x_cells = 4	
    y_cells = 2
    fin_u = 12
    #gate_u = int(sys.argv[4])
    gate = 2
    fin = 2*((fin_u+1)//2)
    gateDummy = 3 ### Total Dummy gates per unit cell 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell 2*finDummy

    uc = fabric_CMC_NMOS_v1_default.UnitCell( fin_u, fin, finDummy, gate, gateDummy)

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy)

    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cmc_nmos_big_v1_default"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)
        assert data['bbox'] == data_golden['bbox']
#        assert data == data_golden
        for (x,y) in zip( data['terminals'], data_golden['terminals']):
            x['netName'] = '_'
            y['netName'] = '_'
            assert x == y
