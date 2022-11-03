
from collections import defaultdict
import pysat.solvers
import pysat.formula

class BitVar:
  def __repr__( self):
    return 'BitVar[' + self.nm + ']'

  def __init__( self, s, nm):
    self.s = s
    self.nm = nm
    self.vars = [ s.add_var() ]

  def var( self):
    return self.vars[0]

  def val( self):
    return self.s.h[self.vars[0]]

class EnumVar:
  def __repr__( self):
    return 'EnumVar[' + self.nm + ']' + str(self.vals)

  def __init__( self, s, nm, vals):
    self.s = s
    self.nm = nm
    self.vals = vals
    self.vars = [ s.add_var() for v in vals]
    s.emit_exactly_one( self.vars)

  def var( self, val):
    return self.vars[self.vals.index(val)]

  def val( self):
    return self.vals[ [ self.s.h[v] for v in self.vars].index(True)]

class PossiblyUnknownEnumVar:
  def __repr__( self):
    return 'PossiblyUnknownEnumVar[' + self.nm + ']' + str(self.vals)

  def __init__( self, s, nm, vals):
    self.s = s
    self.nm = nm
    self.vals = vals
    self.vars = [ s.add_var() for v in vals]
    s.emit_at_most_one( self.vars)

    assert len(set(self.vals)) == len(self.vals)

  def var( self, val):
    return self.vars[self.vals.index(val)]

  def val( self):
    values = [ self.s.h[v] for v in self.vars]
    if any(values):
       return self.vals[values.index(True)]
    else:
       return '<UNKNOWN>'

class PowerSetEnumVar:
  def __repr__( self):
    return 'PowerSetEnumVar[' + self.nm + ']' + str(self.vals)

  def __init__( self, s, nm, vals):
    self.s = s
    self.nm = nm
    self.vals = vals
    self.vars = [ s.add_var() for v in vals]

  def var( self, val):
    return self.vars[self.vals.index(val)]

  def val( self):
    return ','.join( [ vl for (vl,vr) in zip(self.vals,self.vars) if self.s.h[vr]])

class BitVec:
  def __repr__( self):
    return 'BitVec[' + self.nm + ',' + str(self.n) + ']'

  def __init__( self, s, nm, n):
    self.s = s
    self.nm = nm
    self.n = n
    self.vars = [ s.add_var() for v in range(self.n)]

  def var( self, idx):
    return self.vars[idx]

  def val( self, idx=None):
    def tr( x): return '1' if x else '0'
    if idx is None:
      return ''.join( [ tr(self.s.h[self.vars[idx]]) for idx in range(self.n)])
    else:
      return self.s.h[self.vars[idx]]

class VarMgr:
  def __init__( self, s):
    self.s = s
    self.nm_map = {}

  def add_var( self, v):
    if v.nm not in self.nm_map:
        self.nm_map[v.nm] = v
    return v

class Tally:
  def __init__( self):
    self.nvars = 0
    self.h = defaultdict( lambda: None)
    self.state = 'UNKNOWN'
    self.solver = pysat.solvers.Glucose4()
    self.cnf = pysat.formula.CNF()

  def dump_cnf(self, fn):
    with open(fn, "wt") as fp:
      self.cnf.to_fp(fp)

  def solve( self, assumptions=None):


    res = self.solver.solve( assumptions=assumptions if assumptions is not None else [])
    if res is True:
      self.state = 'SAT'
    else:
      self.state = 'UNSAT'

    if self.state == 'SAT':
      for i in self.solver.get_model():
        self.h[i if i > 0 else -i] = i > 0

  def solve_limited( self, assumptions=None):
    res = self.solver.solve_limited( assumptions=assumptions if assumptions is not None else [])
    if res is True:
      self.state = 'SAT'
    elif res is None:
      self.state = 'UNKNOWN'
    else:
      self.state = 'UNSAT'

    if self.state == 'SAT':
      for i in self.solver.get_model():
        self.h[i if i > 0 else -i] = i > 0

  def add_var( self):
    self.nvars += 1
    return self.nvars

  def add_clause( self, cl):
    self.solver.add_clause(cl)
    self.cnf.append(cl)
    

  def emit_or_aux( self, a, z):
# a0 | a1 | ... => z
# z => a0 | a1 | ...
    self.add_clause( [Tally.neg(z)] + a)
    for l in a:
       self.add_clause( [Tally.neg(l) , z])

  def emit_or( self, a, z):
    self.emit_or_aux( a, z)

  def emit_and( self, a, z):
    self.emit_or_aux( [ Tally.neg(l) for l in a], Tally.neg(z))

  def emit_equiv( self, x, z):
    self.emit_or( [x], z)

  def emit_implies( self, x, z):
    self.add_clause( [ Tally.neg(x), z])

  def emit_iff( self, x, z):
    self.add_clause( [ Tally.neg(x), z])
    self.add_clause( [ x, Tally.neg(z)])

  def emit_always( self, z):
    self.add_clause( [z])

  def emit_never( self, z):
    self.add_clause( [Tally.neg(z)])

  def emit_at_most_one( self, inps):
    outs = [ self.add_var(), self.add_var()]
    self.emit_tally( inps, outs)
    self.emit_never( outs[1])

  def emit_at_most_one_alt( self, inps):
    for x in inps:
       for y in inps:
          if x < y:
            self.add_clause( [ Tally.neg(x), Tally.neg(y)])

  def emit_at_least_one( self, inps):
    outs = [ self.add_var()]
    self.emit_tally( inps, outs)
    self.emit_always( outs[0])

  def emit_at_least_one_alt( self, inps):
    self.add_clause( inps)

  def emit_exactly_one( self, inps):
    self.emit_at_most_one( inps)
    self.emit_at_least_one( inps)

  def emit_xor( self, a, z):
    self.emit_symmetric( list(range(1,len(a)+1,2)), a, z)

  def emit_symmetric( self, lst, a, z):
    outs = [self.add_var() for i in range(len(a))]
    self.emit_tally( a, outs)

    toOr = []
    for i in lst:
      tmp = self.add_var()
      if i == 0:
        if len(outs) > 0:
          self.emit_and( [Tally.neg(outs[i])], tmp)
        else:
          self.emit_always( tmp)
      elif i < len(a):
        self.emit_and( [outs[i-1],Tally.neg(outs[i])], tmp)
      else:
        self.emit_equiv( outs[i-1], tmp)
      toOr.append( tmp)

    self.emit_or( toOr, z)


  def emit_majority( self, a, z):
    outs = [self.add_var() for i in range(len(a))]
    self.emit_tally( a, outs)

    mid = (len(a)+1)//2
    if mid > 0:
      self.emit_equiv( outs[mid-1], z)
    else:
      self.emit_always( z)


  def emit_tally( self, inps, outs):
    for o in outs[len(inps):]:
       self.emit_never( o)

    while True:
      if len(inps) == 0:
        break
      elif len(inps) == 1:
        if len(outs) > 0:
          self.emit_equiv( inps[0], outs[0])
        break
      else:
        if len(outs) < len(inps):
          outs0,outs1 = outs[:],[]
        else:
          outs0,outs1 = outs[:-1],outs[-1:]
        sub_outs = [ self.add_var() for out in outs0]
        sub_ands = [ self.add_var() for out in sub_outs[:-1]]
        assert len(sub_outs) == len(sub_ands) + 1
        # zip autotruncates
        for (x,z) in zip(sub_outs, sub_ands + outs1):
          self.emit_and( [ x, inps[-1]], z)
        assert 1 + len(sub_ands) == len(sub_outs)
        assert len(sub_outs) == len(outs0)
        for ((x,y),z) in zip(zip([inps[-1]]+sub_ands, sub_outs), outs0):
          self.emit_or( [ x, y], z)

        inps = inps[:-1]
        outs = sub_outs

  @staticmethod
  def neg( var):
    return -var
