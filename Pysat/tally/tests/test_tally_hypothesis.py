from hypothesis import given, example
import hypothesis.strategies as st

from tally.tally import *

@given(st.lists(st.booleans()))
@example([])
@example([True])
@example([True,True])
@example([False])
@example([False,False])
def test_at_most_one_alt_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))

  print("lst:", lst)

  for (idx,v) in enumerate(lst):
    if v:
      s.emit_always(a.var(idx))
    else:
      s.emit_never(a.var(idx))

  s.emit_at_most_one_alt( a.vars)

  s.solve()

  if len( [v for v in lst if v]) <= 1:
    assert s.state == 'SAT'
  else:
    assert s.state == 'UNSAT'

@given(st.lists(st.booleans()))
@example([])
@example([True])
@example([True,True])
@example([False])
@example([False,False])
def test_tally_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))
  b = mgr.add_var( BitVec( s, 'b', len(lst)))

  tally = len([v for v in lst if v])
  print("lst:", lst, tally)

  for (val,var) in zip(lst,a.vars):
    if val:
      s.emit_always( var)
    else:
      s.emit_never( var)

  if tally > 0:
    s.emit_always(b.var(tally-1))
  if tally < len(lst):
    s.emit_never(b.var(tally))

  s.emit_tally( a.vars, b.vars)
  s.solve()
  assert s.state == 'SAT'

@given(st.lists(st.booleans()))
@example([True,True,True])
@example([True,False,True])
def test_xor_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))
  z = mgr.add_var( BitVar( s, 'z'))

  tally = len([v for v in lst if v])
  print("xor lst:", lst, tally)

  for (val,var) in zip(lst,a.vars):
    if val:
      s.emit_always( var)
    else:
      s.emit_never( var)

  if tally % 2 == 1:
    s.emit_always(z.var())
  else:
    s.emit_never(z.var())

  s.emit_xor( a.vars, z.var())
  s.solve()
  assert s.state == 'SAT'

@given(st.lists(st.booleans()))
@example([True,True,True])
@example([True,False,True])
def test_xnor_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))
  z = mgr.add_var( BitVar( s, 'z'))

  tally = len([v for v in lst if v])
  true_tallys = list(range(0,len(lst)+1,2))
  print("xnor lst:", lst, tally, true_tallys)

  for (val,var) in zip(lst,a.vars):
    if val:
      s.emit_always( var)
    else:
      s.emit_never( var)

  if tally % 2 == 0:
    s.emit_always(z.var())
  else:
    s.emit_never(z.var())

  s.emit_symmetric( true_tallys, a.vars, z.var())
  s.solve()
  assert s.state == 'SAT'

@given(st.lists(st.booleans()))
@example([True,True,True])
@example([True,False,True])
def test_symmetric_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))
  z = mgr.add_var( BitVar( s, 'z'))

  tally = len([v for v in lst if v])
  true_tallys = list(range( (len(lst)+1)//2, len(lst)+1))
  print("majority lst:", lst, tally, true_tallys)

  for (val,var) in zip(lst,a.vars):
    if val:
      s.emit_always( var)
    else:
      s.emit_never( var)

  if tally in true_tallys:
    s.emit_always(z.var())
  else:
    s.emit_never(z.var())

  s.emit_symmetric( true_tallys, a.vars, z.var())
  s.solve()
  assert s.state == 'SAT'

@given(st.lists(st.booleans()))
@example([])
@example([True,True,True])
@example([True,False,True])
def test_majority_hypothesis(lst):
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVec( s, 'a', len(lst)))
  z = mgr.add_var( BitVar( s, 'z'))

  tally = len([v for v in lst if v])
  print("majority lst:", lst, tally)

  for (val,var) in zip(lst,a.vars):
    if val:
      s.emit_always( var)
    else:
      s.emit_never( var)

  if tally >= (len(lst)+1)//2:
    s.emit_always(z.var())
  else:
    s.emit_never(z.var())

  s.emit_majority( a.vars, z.var())
  s.solve()
  assert s.state == 'SAT'
