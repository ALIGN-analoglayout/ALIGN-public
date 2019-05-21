from primitives.fabric_gf import *
import pytest

def test_h():
    c = Canvas()

    c.m2 = StopPointGrid( "m2", "metal1", "h", width=10, pitch=20, offset=0)
    c.m2.addGridPoint(  0, False)
    c.m2.addGridPoint( 10, True)
    c.m2.addGridPoint( 20, False)
    
    assert c.m2.n == 2

    seg = c.addSegment( c.m2, "a", 1, -1, 1)
    assert seg['rect'] == [ -10, 15, 10, 25]

    seg = c.addSegment( c.m2, "a", 1, (7,-1), (7,1))
    assert seg['rect'] == [ 130, 15, 150, 25]

def test_v():
    c = Canvas()

    c.m1 = StopPointGrid( "m1", "metal1", "v", width=10, pitch=20, offset=0)
    c.m1.addGridPoint(  0, False)
    c.m1.addGridPoint( 10, True)
    c.m1.addGridPoint( 20, False)
    
    assert c.m1.n == 2

    seg = c.addSegment( c.m1, "a", 1, -1, 1)
    assert seg['rect'] == [ 15, -10, 25, 10]

    seg = c.addSegment( c.m1, "a", 1, (7,-1), (7,1))
    assert seg['rect'] == [ 15, 130, 25, 150]

    c.computeBbox()
    assert c.bbox.toList() == [ 15, -10, 25, 150]


def test_render_construction_line():
    c = Canvas()

    c.m2 = StopPointGrid( "m2", "metal1", "h", width=10, pitch=20, offset=0)
    c.m2.addGridPoint(  0, False)
    c.m2.addGridPoint( 10, True)
    c.m2.addGridPoint( 20, False)
    
    assert c.m2.n == 2

    with pytest.raises(AssertionError):
        c.addSegment( c.m2, "a", 1, 0, 1)

    with pytest.raises(AssertionError):
        c.addSegment( c.m2, "a", 1, -1, 0)

    with pytest.raises(AssertionError):
        c.addSegment( c.m2, "a", 1, (7,-1), (9,0))


def test_nunit():
    c = Canvas()    
    c.nunit( 0, 0)
    c.computeBbox()

    assert c.bbox.toList() == [-360, -3080, 1800, 3080]

def test_cunit():
    c = Canvas()    
    c.cunit( 0, 0)
    c.computeBbox()

    assert c.bbox.toList() == [-360, -3080, 1800, 3080]
    
