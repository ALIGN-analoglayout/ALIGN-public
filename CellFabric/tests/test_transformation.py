
from primitives.transformation import Transformation, Rect, Tech

def test_tech():
    Tech()

def test_rect():
    r = Rect( 1, 2, 2, 3)
    assert repr(r) == "[1, 2, 2, 3]"

def test_rect_canonical():
    r = Rect( 2, 3, 1, 2)    
    assert repr(r.canonical()) == "[1, 2, 2, 3]"

def test_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

def test_Mult0():
    a = Transformation( 0, 10, 1, 1)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (Transformation.mult( b, a)).hit( (0,0))

def test_preMult0():
    a = Transformation( 0, 10, 1, 1)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (a.preMult(b)).hit( (0,0))

def test_postMult0():
    a = Transformation( 0, 10, 1, 1)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (b.postMult(a)).hit( (0,0))

def test_hitRect():
    a = Transformation( 0, 10, 1, 1)
    r = Rect( 0, 1, 0, 2)
    assert Rect( 0, 11, 0, 12).toList() == a.hitRect(r).toList()

def test_repr():
    a = Transformation( 0, 10, 1, 1)    
    assert repr(a) == "oX: 0 oY: 10 sX: 1 sY: 1"

def test_plusOne():
    a = Transformation( 0, 10, 1, -1)
    assert repr(a.plusOneIfMirrored()) == "oX: 0 oY: 11 sX: 1 sY: -1"
    a = Transformation( 0, 10, -1, 1)
    assert repr(a.plusOneIfMirrored()) == "oX: 1 oY: 10 sX: -1 sY: 1"
    a = Transformation( 0, 10, 1, 1)
    assert repr(a.plusOneIfMirrored()) == "oX: 0 oY: 10 sX: 1 sY: 1"
    
