from hypothesis import given, example
import hypothesis.strategies as st

from cktgen.transformation import Tech, Rect, Transformation

@given(st.tuples(st.integers(), st.integers()))
def test_transformation_hit(p):
    a = Transformation( 2, 3, 1, 1)
    q = a.hit( p)
    assert q == (p[0]+2,p[1]+3)

@given(st.tuples(st.integers(), st.integers(), st.integers(), st.integers()))
def test_transformation_hitRect(r):
    a = Transformation( 2, 3, 1, 1)
    q = a.hitRect( Rect( *r))
    assert q.toList() == [r[0]+2,r[1]+3,r[2]+2,r[3]+3]
