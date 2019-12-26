from cell_fabric.transformation import Transformation, Rect

def test_transformation_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_transformation_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

def test_transformation_Mult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (Transformation.mult( b, a)).hit( (0,0))

def test_transformation_preMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (a.preMult(b)).hit( (0,0))

def test_transformation_postMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (b.postMult(a)).hit( (0,0))

def test_repr():
    a = Transformation( 0, 0, 1, 1)
    assert repr(a) == "Transformation(oX=%d, oY=%d, sX=%d, sY=%d)" % (a.oX, a.oY, a.sX, a.sY)

def test_hitRect():
    a = Transformation( 0, 10, -1, 1)
    r = Rect( 0, 0, 1, 1)
    assert a.hitRect(r).canonical().toList() == [-1, 10, 0, 11]
