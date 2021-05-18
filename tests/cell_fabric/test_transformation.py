from align.cell_fabric.transformation import Transformation, Rect

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

def test_genTr():
    oX, oY = 23, 47

    w,h = 100,200

    for orient in [ 'N', 'S', 'FN', 'FS']:

        tr = Transformation.genTr( orient, w=w, h=h)
        tr.oX, tr.oY = 0, 0
        # tr is now just the flipping matrix, no translation

        tr_offset = Transformation( oX=oX, oY=oY)

        tr_center = Transformation( oX=-w//2, oY=-h//2)
        tr_uncenter = Transformation( oX=w//2, oY=h//2)        
        tr_first = tr_uncenter.postMult( tr).postMult( tr_center)
        tr_whole = tr_offset.postMult( tr_first)

        tr_first2 = Transformation.genTr( orient, w=w, h=h)
        tr_whole2 = tr_offset.postMult( tr_first2)

        assert Transformation() == tr_first2.postMult( tr_first2.inv())
        assert Transformation() == tr_first2.inv().postMult( tr_first2)

        assert tr_first == tr_first2
        assert tr_whole == tr_whole2

        assert tr_first.inv() == tr_center.inv().postMult( tr.inv()).postMult( tr_uncenter.inv())
        assert tr_first.inv() == tr_uncenter.postMult( tr).postMult( tr_center)
        assert tr_first.inv() == tr_first

        assert tr_whole.inv() == tr_first.inv().postMult( tr_offset.inv())
