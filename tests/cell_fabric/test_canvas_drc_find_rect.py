import pytest
import pathlib

from align.cell_fabric import Canvas, Pdk, Wire
from align.cell_fabric.drc import DesignRuleCheck
from align.cell_fabric.remove_duplicates import ScanlineRect

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))

    return c,p

def test_A(setup):
    c,p = setup

    m2 = p['M2']

    def gr( x0, x1):
        y = m2['Width']
        return [ x0, -y//2, x1, y//2]

    l = m2['MinL']
    e = m2['EndToEnd']

    dx = 20

    c.terminals = []
    for i in range( 100000):
        c.terminals.append( 
            {'layer': 'M2', 'netName': f'x{i}', 'rect': gr( i*(l+e)-dx, i*(l+e)+l-dx), "netType": "drawing"}
            )

    c.computeBbox()
    c.removeDuplicates()

    c.drc = DesignRuleCheck( c)
    r = ScanlineRect()
    
    for i in range(len(c.terminals)):
        r.rect = [ i*(l+e),0,i*(l+e),0]
        covering_r = c.drc._find_rect_covering_via( r, 'M2', 'H')
        assert covering_r == gr( i*(l+e)-dx, i*(l+e)+l-dx)
