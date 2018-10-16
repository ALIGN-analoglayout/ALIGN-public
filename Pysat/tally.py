#!/usr/bin/env python

import re
import os
import sys
import io
import gzip

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
    return self.vals[map( lambda v: self.s.h[v], self.vars).index(True)]

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
 
class Sat:
  def __init__( self, use_picosat=False, use_eureka=False):
    self.use_picosat = use_picosat
    self.use_eureka  = use_eureka
    self.use_glucose = False
    self.use_parallel_glucose = False
    self.use_minicard = False
    self.unsat_core = None

    self.nvars = 0
    self.clauses = []
    self.cardinality_constraints = []
    self.indicator = 'UNKNOWN'
    self.h = {}
    self.nm_map = {}
    self.important_vars = []
    self.nsols = 1

  def write_dimacs( self, fp):
    nclause_like = len(self.clauses)+len(self.cardinality_constraints)

    tag = "cnf+" if self.cardinality_constraints else "cnf"

    print 'Header: p %s %d %d' % ( tag, self.nvars, nclause_like)
    fp.write( u'p %s %d %d\n' % ( tag, self.nvars, nclause_like))
    for ( cl, op, k) in self.cardinality_constraints:
       for l in cl:
          fp.write( u'%d ' % l)
       fp.write( op)
       fp.write( u' %d\n' % k)
    for cl in self.clauses:
       for l in cl:
          fp.write( u'%d ' % l)
       fp.write( u'0\n')
    print 'Done with write_dimacs'

  def read_unsat_core( self, fn):
     self.unsat_core = []
     with io.open( fn, 'r') as fp:
        for line in fp:
           line = line.rstrip('\n')
           if line[0] == 'p':
              pass
           else:
              vec = map( int, line.split( ' '))
              assert vec[-1] == 0, vec
              self.unsat_core.append( vec[:-1])

  def report_unsat_core( self, mgr, f=None):
     print 'Ready to report unsat core'     
     imap = {}
     for (k,v) in mgr.nm_map.items():
        for (idx,vv) in enumerate(v.vars):
           if f:
              imap[vv] = f( v, idx, vv)
           else:
              imap[vv] = (v.nm,idx)
     for clause in self.unsat_core:
        for lit in clause:
           vv = abs(lit)
           if vv in imap:
              print 'DECODE:', vv, imap[vv]
        print clause

  def write_important_vars( self, fn):
     with open( fn, 'w') as fp:
       fp.write( 'p ilits %d\n' % len(self.important_vars))
       for v in self.important_vars:
          fp.write( '%d 0 0\n' % v)

  def read_minisat_results( self, fn):
     with io.open( '__result', 'r') as fp:
        res = fp.readlines()
        self.indicator = res[0].rstrip('\n')
        if self.indicator == 'SAT':
           model = map( lambda x: int(x), res[1].rstrip('\n').split())
           assert model.pop() == 0
           self.h = {}
           for m in model:
              self.h[abs(m)] = m > 0
        else:
           assert self.indicator == 'UNSAT'

  def read_glucose_results( self, fn):
     with io.open( '__result', 'r') as fp:
        res = fp.readlines()
        self.indicator = res[0].rstrip('\n')
        if self.indicator == 'UNSAT':
           pass
        else:
           self.indicator = 'SAT'
           model = map( lambda x: int(x), res[0].rstrip('\n').split())
           assert model.pop() == 0
           self.h = {}
           for m in model:
              self.h[abs(m)] = m > 0

  def read_parallel_glucose_results( self, fn):


     p_c = re.compile( '^c.*$')
     p_blank = re.compile( '^\s*$')
     p_s = re.compile( '^s (\S+)\s*$')
     p_v = re.compile( '^v .*$')

     with io.open( '__result', 'r') as fp:
        for line in fp:
           line = line.rstrip( '\n')
           m = p_c.match( line)
           if m:
              continue

           m = p_blank.match( line)
           if m:
              continue

           m = p_s.match( line)
           if m:
             self.indicator = m.groups()[0]
             continue
             
           m = p_v.match( line)
           if m:
             model = map( lambda x: int(x), line[2:].split())
             assert model.pop() == 0
             self.h = {}
             for m in model:
               self.h[abs(m)] = m > 0

             continue

           assert False, ('"' + line + '"')



  def solve( self):
    self.h = {}
    self.indicator = 'UNKNOWN'
    with open( '__dimacs', 'w') as fp:
#    with gzip.GzipFile( '__dimacs.gz', 'w') as fp:
      self.write_dimacs( fp)

    if self.use_picosat:
       install_dir = '/nfs/site/disks/scl.work.46/ppt/users/smburns/fabrics/picosat-936'

       os.system( install_dir + '/picosat -v -c __unsat_core -o __result __dimacs')

       model = []

       with io.open( '__result', 'r') as fp:
         for line in fp:
            line = line.rstrip('\n')
            if   line[0] == 'c':
               pass
            elif line[0] == 's':
               if line[2:] == 'SATISFIABLE':
                  self.indicator = 'SAT'
               elif line[2:] == 'UNSATISFIABLE':
                  self.indicator = 'UNSAT'
               else:
                  assert False, line
            elif line[0] == 'v':
               model += map( int, line[2:].split( ' '))
            else:
               assert False

       if self.indicator == 'SAT':
         assert model.pop() == 0
         self.h = {}
         for m in model:
             self.h[abs(m)] = m > 0
       elif self.indicator == 'UNSAT':
         print 'Unsatisfiable'
         self.read_unsat_core( '__unsat_core')

    elif self.use_eureka:
      
       os.environ['CAD_ROOT'] = '/p/dt/cad/em64t_SLES10'

       install_dir = os.environ['CAD_ROOT'] + '/prover/12.2_rc1_stOpt64/bin'

       os.system( 'rm -f __dimacs.ilits')

       if self.important_vars == []:
          self.write_important_vars( '__dimacs.ilits')
          os.system( install_dir + '/eureka_tool __dimacs > __result')
       else:
          self.write_important_vars( '__dimacs.ilits')
          os.system( install_dir + ( '/eureka_tool __dimacs -preprocess 1 -allsat 1 -force_diff_models_strat 0 -cex_max_num %d > __result' % self.nsols))


       model = []

       p_model = re.compile( '^Model\s+(\S+)\s*$')
       p_enum = re.compile( '^Enum:\s+(\S.*)$')

       self.all_models = []

       with io.open( '__result', 'r') as fp:
         for line in fp:
            line = line.rstrip('\n')

            if line == "":
               pass
            elif line[0] == 'c':
               pass
            elif line[0] == 's':
               if line[2:] == 'SATISFIABLE':
                  self.indicator = 'SAT'
               elif line[2:] == 'UNSATISFIABLE':
                  if self.indicator != 'SAT':
                     self.indicator = 'UNSAT'
               else:
                  assert False, line
            elif line[0] == 'v':
               self.indicator = 'SAT'
               lst = filter( lambda x: x != '', line[2:].split( ' '))
               model += map( int, lst)
            else:
               m = p_model.match( line)
               if m:
                  continue             

               m = p_enum.match( line)
               if m:
                  self.all_models.append( [ int(x) for x in m.groups()[0].split()])
                  continue             

               assert False, line
     
       if self.important_vars != []:
          print "# of models: %d (limit %d)" % ( len( self.all_models), self.nsols)

       if self.indicator == 'SAT' and self.all_models == []:
         assert model.pop() == 0
         self.h = {}
         for m in model:
             self.h[abs(m)] = m > 0
       elif self.indicator == 'UNSAT':
         if self.important_vars == []:
            print 'Unsatisfiable'
            self.read_unsat_core( '__unsat_core')

    elif self.use_glucose:
       install_dir = '/nfs/site/disks/scl.work.46/ppt/users/smburns/FABRIC_ENV/glucose/glucose-syrup/simp'

       os.system( install_dir + '/glucose -cl-lim=-1 -verb=2 -minSizeMinimizingClause=120 __dimacs __result')
       self.read_glucose_results( '__result')

    elif self.use_parallel_glucose:
       install_dir = '/nfs/site/disks/scl.work.46/ppt/users/smburns/FABRIC_ENV/glucose/glucose-syrup/parallel'

       os.system( install_dir + '/glucose-syrup -model __dimacs > __result')
       self.read_parallel_glucose_results( '__result')

    elif self.use_minicard:
       install_dir = '/nfs/site/disks/scl.work.46/ppt/users/smburns/FABRIC_ENV/minicard/minicard/minicard'

       os.system( install_dir + '/minicard_static __dimacs __result')
       self.read_minisat_results( '__result')

    else:
       if 'VIRTUAL_ENV' in os.environ:
          install_dir = os.environ['VIRTUAL_ENV'] + '/minisat-install'
       else:
          install_dir = '/home/saasbook/python-ext/minisat/minisat-install'
#          install_dir = '/nfs/site/disks/scl.work.46/ppt/users/smburns/fabrics/minisat-install'

       os.environ['LD_LIBRARY_PATH'] = install_dir + '/lib'
#       os.system( install_dir + '/bin/minisat __dimacs.gz __result')
       os.system( install_dir + '/bin/minisat __dimacs __result')
       self.read_minisat_results( '__result')
#       os.system( 'rm -f __dimacs __result')

  def add_var( self):
    self.nvars += 1
    return self.nvars

  def add_clause( self, cl):
    self.clauses.append( cl)

  def add_cardinality_constraint( self, cl, op, k):
    self.cardinality_constraints.append( (cl, op, k))

  def emit_or_aux( self, a, z):
# a0 | a1 | ... => z 
# z => a0 | a1 | ... 
    self.add_clause( [Sat.neg(z)] + a)
    for l in a:
       self.add_clause( [Sat.neg(l) , z])

  def emit_or( self, a, z):
    self.emit_or_aux( a, z)

  def emit_and( self, a, z):
    self.emit_or_aux( map( Sat.neg, a), Sat.neg(z))

  def emit_equiv( self, x, z):
    self.emit_or( [x], z)

  def emit_implies( self, x, z):
    self.add_clause( [ Sat.neg(x), z])

  def emit_iif( self, x, z):
    self.add_clause( [ Sat.neg(x), z])
    self.add_clause( [ x, Sat.neg(z)])

  def emit_always( self, z):
    self.add_clause( [z])

  def emit_never( self, z):
    self.add_clause( [Sat.neg(z)])

  def emit_at_most_one( self, inps):
#
#    for x in inps:
#       for y in inps:
#          if x < y:
#            self.add_clause( [ Sat.neg(x), Sat.neg(y)])
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

if __name__ == "__main__":

   import argparse

   parser = argparse.ArgumentParser( description="Compute Finite Projective Plane of Order n Straight from Definition")

   parser.add_argument( '-use_picosat', action='store_true')
   parser.add_argument( '-use_eureka', action='store_true')
   parser.add_argument( '-use_glucose', action='store_true')
   parser.add_argument( '-use_parallel_glucose', action='store_true')
   parser.add_argument( '-use_minicard', action='store_true')

   args = parser.parse_args()

   s = Sat()

   if args.use_picosat: s.use_picosat = True
   if args.use_eureka: s.use_eureka = True
   if args.use_glucose: s.use_glucose = True
   if args.use_parallel_glucose: s.use_parallel_glucose = True
   if args.use_minicard: s.use_minicard = True

   mgr = VarMgr( s)

   if False:
     a = mgr.add_var( BitVar( s, 'a'))
     s.emit_never( a.var())
     s.emit_always( a.var())
     s.solve()
     if s.indicator == 'UNSAT':
       if s.unsat_core is not None:
         s.report_unsat_core( mgr)

   if False:
     a = mgr.add_var( BitVec( s, 'a', 8))
     s.emit_never( a.var( 0))
     s.emit_always( a.var( 0))
     s.solve()
     if s.indicator == 'UNSAT':
       if s.unsat_core is not None:
         s.report_unsat_core( mgr)

   if True:
     a = mgr.add_var( BitVec( s, 'a', 8))
     s.emit_never( a.var( 0))

     s.add_cardinality_constraint( [a.var(i) for i in range(8)], ">=", 7) 

     s.solve()
     if s.indicator == 'UNSAT':
       if s.unsat_core is not None:
         s.report_unsat_core( mgr)

