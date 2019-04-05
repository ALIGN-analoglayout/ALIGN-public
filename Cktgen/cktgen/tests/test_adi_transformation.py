
from cktgen.cktgen import ADITransform

class TestADITransform:
  def test_hit0( self):
    trans = ADITransform()
    assert (0,0) == trans.hit( (0,0))
  def test_hit1( self):
    trans = ADITransform()
    assert (100,50) == trans.hit( (100,50))
  def test_hit2( self):
    trans = ADITransform.translate( 100, -50)
    assert (200,0) == trans.hit( (100,50))
  def test_hit3( self):
    trans = ADITransform.mirrorAcrossXAxis()
    assert (100,-50) == trans.hit( (100,50))
  def test_hit4( self):
    trans = ADITransform.mirrorAcrossYAxis()
    assert (-100,50) == trans.hit( (100,50))
  def test_preMult0( self):
    trans0 = ADITransform.mirrorAcrossYAxis()
    trans1 = ADITransform.translate( 100, -50)
    trans = trans1.preMult(trans0)
    pt = (100,50)
    assert trans.hit( pt) == trans0.hit( trans1.hit( pt))
  def test_preMult1( self):
    trans0 = ADITransform.mirrorAcrossYAxis()
    trans1 = ADITransform.translate( -100, -50)
    trans = trans1.preMult(trans0)
    pt = (100,-50)
    assert trans.hit( pt) == trans0.hit( trans1.hit( pt))
