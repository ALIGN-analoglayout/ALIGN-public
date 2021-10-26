
import pathlib

from align.cell_fabric import Pdk
from align.primitive.default import DefaultCanvas
from align.cell_fabric.routing_collateral import MetalTemplate

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

def test_one():
    p = Pdk().load(pdkfile)
    c = DefaultCanvas(p)
    assert c.generate_routing_collateral( mydir / "routing_collateral_cand")

def test_m3():
    p = Pdk().load(pdkfile)
    c = DefaultCanvas(p)

    m = c.generators['m3'] 
    mt = MetalTemplate(m)

    #print( "m3 clg grid", m.clg.grid, "m3 clg legal indices", m.clg.legalIndices)
    #print( "m3 spg grid", m.spg.grid, "m3 spg legal indices", m.spg.legalIndices)

    assert 1 in m.spg.legalIndices
    assert 3 in m.spg.legalIndices
 ### The following assertions are modified based on the updtaed PDK
    assert m.spg.grid[1][0] == 36 
    assert m.spg.grid[3][0] == 48 

    assert mt.widths == [40,40,40]
    assert mt.colors == ["c1","c2","c1"]
    assert mt.spaces == [40,40]
    assert mt.offset == 0

    assert mt.stop_offset == 36 
    assert mt.stops == [12,72]
