import pytest
from tally.tally import *

@pytest.fixture
def one_bit():
  s = Tally()
  mgr = VarMgr( s)
  a_bv = mgr.add_var( BitVar( s, 'a'))
  a = a_bv.var()
  assert 'BitVar[a]' == str(a_bv)
  return s, mgr, a_bv, a

@pytest.fixture
def two_bits():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b']
  [a,b] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  return s, mgr, a, b

def test_one_variable_contradiction(one_bit):
  s, _, _, a = one_bit
  s.emit_never( a)
  s.emit_always( a)
  s.solve()
  assert s.state == 'UNSAT'

def test_one_variable_contradiction_limited(one_bit):
  s, _, _, a = one_bit
  s.emit_never( a)
  s.emit_always( a)
  s.solve_limited()
  assert s.state == 'UNSAT'

def test_one_variable_T(one_bit):
  s, mgr, _, a = one_bit
  s.emit_always( a)
  s.solve()
  assert s.state == 'SAT'
  assert mgr.nm_map['a'].val()

def test_one_variable_F(one_bit):
  s, mgr, _, a = one_bit
  s.emit_never( a)
  s.solve()
  assert s.state == 'SAT'
  assert not mgr.nm_map['a'].val()

def test_one_variable_F_limited(one_bit):
  s, mgr, _, a = one_bit
  s.emit_never( a)
  s.solve_limited()
  assert s.state == 'SAT'
  assert not mgr.nm_map['a'].val()

def test_implies(two_bits):
  s, _, a, b = two_bits
  s.emit_implies( a, b)
  s.solve(assumptions=[ a, b])
  assert s.state == 'SAT'
  s.solve(assumptions=[-a,-b])
  assert s.state == 'SAT'
  s.solve(assumptions=[-a, b])
  assert s.state == 'SAT'
  s.solve(assumptions=[ a,-b])
  assert s.state == 'UNSAT'

def test_iff(two_bits):
  s, _, a, b = two_bits
  s.emit_iff( a, b)
  s.solve(assumptions=[ a, b])
  assert s.state == 'SAT'
  s.solve(assumptions=[-a,-b])
  assert s.state == 'SAT'
  s.solve(assumptions=[-a, b])
  assert s.state == 'UNSAT'
  s.solve(assumptions=[ a,-b])
  assert s.state == 'UNSAT'

def test_enum_var():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( EnumVar( s, 'a', ['one','two','three']))
  assert str(a) == "EnumVar[a]['one', 'two', 'three']"
  s.emit_always( a.var( 'one'))
  s.solve()
  assert s.state == 'SAT'
  assert 'one' == mgr.nm_map['a'].val()

def test_possibly_unknown_enum_var():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( PossiblyUnknownEnumVar( s, 'a', ['one','two','three']))
  s.emit_never( a.var( 'one'))
  s.emit_never( a.var( 'two'))
  s.emit_never( a.var( 'three'))
  s.solve()
  assert s.state == 'SAT'
  assert '<UNKNOWN>' == mgr.nm_map['a'].val()

def test_possibly_unknown_enum_vara():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( PossiblyUnknownEnumVar( s, 'a', ['one','two','three']))
  assert "PossiblyUnknownEnumVar[a]['one', 'two', 'three']" == str(a)
  s.emit_never( a.var( 'one'))
  s.emit_never( a.var( 'two'))
  s.emit_always( a.var( 'three'))
  s.solve()
  assert s.state == 'SAT'
  assert 'three' == mgr.nm_map['a'].val()

def test_tally_more_outs():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','aa','bb','cc']
  [a,b,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b],[aa,bb,cc])
  s.emit_always( a)
  s.emit_always( b)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert mgr.nm_map['aa'].val()
  assert mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_power_set_enum_var():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( PowerSetEnumVar( s, 'a', ['one','two','three']))
  assert "PowerSetEnumVar[a]['one', 'two', 'three']" == str(a)
  s.emit_never( a.var( 'one'))
  s.emit_always( a.var( 'two'))
  s.emit_always( a.var( 'three'))
  s.solve()
  assert s.state == 'SAT'
  assert 'two,three' == mgr.nm_map['a'].val()

def test_bit_vec():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', 3))
  assert 'BitVec[a,3]' == str(a)
  s.emit_never( a.var( 0))
  s.emit_always( a.var( 1))
  s.emit_always( a.var( 2))
  s.solve()
  assert s.state == 'SAT'
  assert '011' == mgr.nm_map['a'].val()
  assert mgr.nm_map['a'].val(0) is False
  assert mgr.nm_map['a'].val(1) is True
  assert mgr.nm_map['a'].val(2) is True

def test_at_most_one_alt():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', 3))
  assert 'BitVec[a,3]' == str(a)
  s.emit_never( a.var( 0))
  s.emit_always( a.var( 1))
  s.emit_always( a.var( 2))
  s.emit_at_most_one_alt( a.vars)
  s.solve()
  assert s.state == 'UNSAT'

def test_at_least_one_alt():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', 3))
  assert 'BitVec[a,3]' == str(a)
  s.emit_never( a.var( 0))
  s.emit_always( a.var( 1))
  s.emit_always( a.var( 2))
  s.emit_at_least_one_alt( a.vars)
  s.solve()
  assert s.state == 'SAT'


def test_tally_zero_inputs():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['aa','bb','cc']
  [aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [],[aa,bb,cc])
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert not mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_tally_one_input():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','aa','bb','cc']
  [a,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a],[aa,bb,cc])
  s.emit_always( a)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert     mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_tally_3():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','c','aa','bb','cc']
  [a,b,c,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b,c],[aa,bb,cc])
  s.emit_never( a)
  s.emit_always( b)
  s.emit_always( c)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert mgr.nm_map['aa'].val()
  assert mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_tally_3a():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','c','aa','bb','cc']
  [a,b,c,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b,c],[aa,bb,cc])
  s.emit_never( a)
  s.emit_never( b)
  s.emit_never( c)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert not mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_tally_6_2():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','c','d','e','f','aa','bb']
  [a,b,c,d,e,f,aa,bb] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b,c,d,e,f],[aa,bb])
  s.emit_never( a)
  s.emit_never( b)
  s.emit_never( c)
  s.emit_always( d)
  s.emit_never( e)
  s.emit_never( f)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert     mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()

def test_tally_6_2a():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','c','d','e','f','aa','bb']
  [a,b,c,d,e,f,aa,bb] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b,c,d,e,f],[aa,bb])
  s.emit_never( a)
  s.emit_always( b)
  s.emit_never( c)
  s.emit_always( d)
  s.emit_never( e)
  s.emit_always( f)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert     mgr.nm_map['aa'].val()
  assert     mgr.nm_map['bb'].val()

def test_tally_2_3():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','aa','bb','cc']
  [a,b,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b],[aa,bb,cc])
  s.emit_never( a)
  s.emit_never( b)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])
  assert not mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()

def test_tally_2_3_as_0_or_2():
  s = Tally()
  mgr = VarMgr( s)
  nms = ['a','b','aa','bb','cc']
  [a,b,aa,bb,cc] = [ mgr.add_var( BitVar( s, nm)).var() for nm in nms]
  s.emit_tally( [a,b],[aa,bb,cc])

  s.add_clause([-aa, -cc])
  s.add_clause([-aa, bb])

  s.emit_always( a)
  s.emit_never( b)
  s.solve()
  assert s.state == 'SAT'
  print( [ mgr.nm_map[nm].val() for nm in nms])

  assert mgr.nm_map['aa'].val()
  assert not mgr.nm_map['bb'].val()
  assert not mgr.nm_map['cc'].val()


def tally_instance(n=2, m=3):
  s = Tally()
  mgr = VarMgr( s)

  inps_nms = [chr(ord('a') + i) for i in range(n)]
  outs_nms = [''.join(chr(ord('a') + i)*2) for i in range(m)]

  inps = [ mgr.add_var( BitVar( s, nm)).var() for nm in inps_nms]
  outs = [ mgr.add_var( BitVar( s, nm)).var() for nm in outs_nms]

  s.emit_tally(inps, outs)

  return s, mgr, inps_nms + outs_nms, inps, outs

@pytest.mark.parametrize("n,m", [(2, 3), (10,10), (12, 2)])
def test_tally_exhaustive(n, m):

  for i in range(1<<n):
    s, mgr, nms, inps, outs = tally_instance(n, m)

    count = 0
    for j in range(n):
      if ((1<<j) & i) != 0:
        count += 1
        s.emit_always(inps[j])
      else:
        s.emit_never(inps[j])

    for j in range(m):
      if count > j:
        s.emit_always(outs[j])
      else:
        s.emit_never(outs[j])        

    s.solve()
    assert s.state == 'SAT', (i,count)
    print( i, count, [ mgr.nm_map[nm].val() for nm in nms])  


def test_hard_limited():
  s = Tally()
  m = 15
  n = 15
  rows = [ [ s.add_var() for j in range(n)] for i in range(m)]

  cols = []
  for idx in range(n):
    l = []
    for row in rows:
      l.append( row[idx])
    cols.append(l)

  def less_eq( limit, vecs):
    for vec in vecs:
      tmp = [ s.add_var() for i in range(limit+1)]
      s.emit_tally( vec, tmp)
      s.emit_never( tmp[-1])

  def greater_eq( limit, vecs):
    for vec in vecs:
      tmp = [ s.add_var() for i in range(limit)]
      s.emit_tally( vec, tmp)
      s.emit_always( tmp[-1])

  less_eq( 1, rows)
  greater_eq( 2, cols)

  s.solver.conf_budget(1000)
  s.solver.prop_budget(1000)
  s.solve_limited()
  assert s.state == 'UNKNOWN'
