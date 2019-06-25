
from cell_fabric import DefaultCanvas, Pdk
from cell_fabric.routing_collateral import MetalTemplate

def test_one():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)
    assert c.generate_routing_collateral( "tests/routing_collateral_cand")

def test_m3():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)

    m = c.generators['m3'] 
    mt = MetalTemplate(m)

    print( "m3 clg grid", m.clg.grid, "m3 clg legal indices", m.clg.legalIndices)
    print( "m3 spg grid", m.spg.grid, "m3 spg legal indices", m.spg.legalIndices)

    assert 1 in m.spg.legalIndices
    assert 3 in m.spg.legalIndices
    assert m.spg.grid[1][0] == 80
    assert m.spg.grid[3][0] == 80

    assert mt.widths == [40,40,40]
    assert mt.colors == ["c1","c2","c1"]
    assert mt.spaces == [40,40]
    assert mt.offset == 40 # Why not zero? is the grid offset on purpose

    assert mt.stop_offset == 80 # Why not zero? [should mean the same thing]
    assert mt.stops == [80]
