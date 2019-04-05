
from cktgen.cktgen import ADITransform

def test_hit0():
  trans = ADITransform()
  assert (0,0) == trans.hit( (0,0))

def test_hit1():
  trans = ADITransform()
  assert (100,50) == trans.hit( (100,50))

def test_hit2():
  trans = ADITransform.translate( 100, -50)
  assert (200,0) == trans.hit( (100,50))

def test_hit3():
  trans = ADITransform.mirrorAcrossXAxis()
  assert (100,-50) == trans.hit( (100,50))

def test_hit4():
  trans = ADITransform.mirrorAcrossYAxis()
  assert (-100,50) == trans.hit( (100,50))

def test_preMult0():
  trans0 = ADITransform.mirrorAcrossYAxis()
  trans1 = ADITransform.translate( 100, -50)
  trans = trans1.preMult(trans0)
  pt = (0,0)
  assert trans.hit( pt) == trans0.hit( trans1.hit( pt))
  pt = (100,0)
  assert trans.hit( pt) == trans0.hit( trans1.hit( pt))
  pt = (0,100)
  assert trans.hit( pt) == trans0.hit( trans1.hit( pt))

def test_repr():
  a = ADITransform()
  assert a == eval(repr(a)) # nosec

def test_copy():
  a = ADITransform()
  assert a == a.copy()
