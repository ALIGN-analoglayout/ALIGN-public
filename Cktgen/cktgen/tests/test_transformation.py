
from cktgen.transformation import Tech, Rect, Transformation

def test_Tech():
    Tech()


def test_Rect():
    r0 = Rect(   0, 0, 100, 100)
    r1 = Rect( 100, 0,   0, 100)
    assert r0.canonical().toList() == r1.canonical().toList()
    assert repr(r0) == "[0, 0, 100, 100]"

def test_Transformation_eq():
    t0 = Transformation( 0, 10)    
    t1 = Transformation( 0, 10, 1, -1)    
    t2 = Transformation( 0, 10)
    assert repr(t0) != repr(t1)
    assert t0 != None
    assert t0 != t1
    assert t0 == t2

def test_Transformation_plus():
    t0 = Transformation( 0, 0, 1, -1)    
    t1 = Transformation( 0, 1, 1, -1)    
    assert t1 == t0.plusOneIfMirrored()
    t0 = Transformation( 0, 0, -1, -1)    
    t1 = Transformation( 1, 1, -1, -1)    
    assert t1 == t0.plusOneIfMirrored()
    t0 = Transformation( 0, 0,  1,  1)    
    t1 = Transformation( 0, 0,  1,  1)    
    assert t1 == t0.plusOneIfMirrored()
    t0 = Transformation( 0, 0, -1,  1)    
    t1 = Transformation( 1, 0, -1,  1)    
    assert t1 == t0.plusOneIfMirrored()


def test_Transformation_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_Transformation_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

def test_Transformation_Mult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (Transformation.mult( b, a)).hit( (0,0))

def test_Transformation_preMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (a.preMult(b)).hit( (0,0))

def test_Transformation_postMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (b.postMult(a)).hit( (0,0))


