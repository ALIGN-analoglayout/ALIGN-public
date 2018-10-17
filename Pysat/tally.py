#!/usr/bin/env python

import re
import os
import sys
import io
import gzip

import pysat.solvers

class BitVar:
  def __init__( self, s, nm):
    self.s = s
    self.nm = nm
    self.vars = [ s.add_var() ]

  def var( self):
    return self.vars[0]

  def val( self):
    return self.s.h[self.vars[0]]

  def __repr__( self):
    return 'Var(' + self.nm + ')'

class EnumVar:
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
    values = map( lambda v: self.s.h[v], self.vars)
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


  def val( self):

    def tr( x):
      return '1' if x else '0'

    return ''.join( [ tr(self.s.h[self.vars[idx]]) for idx in range(self.n)])

class VarMgr:
  def __init__( self, s):
    self.s = s
    self.nm_map = {}

  def add_var( self, v):  
    if v.nm not in self.nm_map:
        self.nm_map[v.nm] = v
    return v
 
from collections import defaultdict

class Tally:
  def __init__( self):
    self.nvars = 0
    self.nm_map = {}
    self.h = defaultdict( list)
    self.state = 'UNKNOWN'
    self.solver = pysat.solvers.Glucose4()

  def solve( self):
    res = self.solver.solve()
    if res == True:
      self.state = 'SAT'
    else:
      self.state = 'UNSAT'

    for i in self.solver.get_model():
      self.h[i if i > 0 else -i] = i > 0

  def add_var( self):
    self.nvars += 1
    return self.nvars

  def add_clause( self, cl):
    self.solver.add_clause( cl)

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

  def emit_iif( self, x, z):
    self.add_clause( [ Tally.neg(x), z])
    self.add_clause( [ x, Tally.neg(z)])

  def emit_always( self, z):
    self.add_clause( [z])

  def emit_never( self, z):
    self.add_clause( [Tally.neg(z)])

  def emit_at_most_one( self, inps):
#
#    for x in inps:
#       for y in inps:
#          if x < y:
#            self.add_clause( [ Tally.neg(x), Tally.neg(y)])
    outs = [ self.add_var(), self.add_var()]
    self.emit_tally( inps, outs)
    self.emit_never( outs[1])

  def emit_at_least_one( self, inps):
#    self.add_clause( inps)
    outs = [ self.add_var()]
    self.emit_tally( inps, outs)
    self.emit_always( outs[0])


  def emit_exactly_one( self, inps):
    self.emit_at_most_one( inps)
    self.emit_at_least_one( inps)

  def emit_tally( self, inps, outs):
    print( "emit_tally", inps, outs)

    for o in outs[len(inps):]:
       self.emit_never( o)

    if len(inps) == 0:
       pass
    elif len(inps) == 1:
       if len(outs) > 0:
          self.emit_equiv( inps[0], outs[0])
    elif len(inps) == 2:
       if len(outs) > 0:
          self.emit_or( inps, outs[0])
       if len(outs) > 1:
          self.emit_and( inps, outs[1])
    else:           
       if len(outs) < len(inps):
          outs0,outs1 = outs[:],[]
       else:
          outs0,outs1 = outs[:-1],outs[-1:]
       sub_outs = [ self.add_var() for out in outs0]
       self.emit_tally( inps[:-1], sub_outs)
       sub_ands = [ self.add_var() for out in sub_outs[:-1]]
       assert len(sub_outs) == len(sub_ands) + 1
# zip autotruncates 
       for (x,z) in zip(sub_outs, sub_ands + outs1):
          self.emit_and( [ x, inps[-1]], z)
       assert 1 + len(sub_ands) == len(sub_outs)
       assert len(sub_outs) == len(outs0)
       for ((x,y),z) in zip(zip([inps[-1]]+sub_ands, sub_outs), outs0):
          self.emit_or( [ x, y], z)
#    print 'end emit_tally', len(inps), len(outs)

  def assoc_pairs( self, nm_pairs):
    for p,q in nm_pairs:
       self.nm_map[p] = q

  @staticmethod
  def neg( var):
    return -var

def test_one_variable_contradiction():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVar( s, 'a')).var()
  s.emit_never( a)
  s.emit_always( a)
  assert not s.solver.solve()
  assert s.solver.get_model() is None

def test_one_variable_T():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVar( s, 'a')).var()
  s.emit_always( a)
  s.solve()
  assert s.state == 'SAT'
  assert mgr.nm_map['a'].val()

def test_one_variable_F():
  s = Tally()
  mgr = VarMgr( s)
  a = mgr.add_var( BitVar( s, 'a')).var()
  s.emit_never( a)
  s.solve()
  assert s.state == 'SAT'
  assert not mgr.nm_map['a'].val()
    
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


if __name__ == "__main__":
  import argparse
  parser = argparse.ArgumentParser( description="Tally Circuits and other helpers around pysat")
  args = parser.parse_args()
