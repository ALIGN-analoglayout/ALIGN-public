import pytest
import itertools
import math

from cell_fabric import DefaultCanvas, Pdk, Wire, Via

@pytest.fixture
def setup():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)
    return c

def test_m1_pex(setup):
    c = setup
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]}]
    c.gen_data()
    assert len(c.pex.netCells) == math.ceil(300 / c.pdk['Poly']['Pitch'])

def test_m2_pex(setup):
    c = setup
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 300, 100]}]
    c.gen_data()
    assert len(c.pex.netCells) == math.ceil(300 / c.pdk['Poly']['Pitch'])

def test_via_pex(setup):
    c = setup
    for (i,nm) in itertools.chain( itertools.product( [0,2,4], ['a']), itertools.product( [1,3,5], ['b'])):
        c.addWire( c.m1, nm, None, i, (0,-1), (3,-1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +b======+=======*
                    b
+a======+=======+   |
                    |
    +b======+=======/
""")
    c.gen_data()
    from pprint import pprint
    pprint(c.pex.netCells)
    assert len(c.pex.netCells) == 48
