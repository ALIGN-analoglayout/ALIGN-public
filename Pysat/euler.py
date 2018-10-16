#!/usr/bin/env python

import sys
sys.path.append( '..')
sys.path.append( '../..')

import sets
import networkx as nx
import pysat
import os
import re

def cr( g, e):
  G = g.copy()
  G.remove_edge( e[0], e[1], key=e[2])
  return G

def se( g, n):
  return g.number_of_edges() == 1 and len(g.edges(n)) == 1

def all_euler_pair_paths( t0, t1):
   (g0, n0) = t0
   (g1, n1) = t1

   if se( g0, n0) and se( g1, n1):
      e0 = g0.edges(n0,keys=True,data=True)[0]
      e1 = g1.edges(n1,keys=True,data=True)[0]
      if e0[3]['label'] == e1[3]['label']: # Labels equal
         return [([e0],[e1])]
   
   QQQ = [ ([e0] + p0,[e1] + p1) 
               for e0 in g0.edges(n0,keys=True,data=True)
               for e1 in g1.edges(n1,keys=True,data=True)
               if e0[3]['label'] == e1[3]['label']
               for (p0,p1) in all_euler_pair_paths( (cr(g0,e0), e0[1]), (cr(g1,e1), e1[1])) ]
   
   return QQQ


def all_euler_paths(g, n):
    if se( g, n):
       return [g.edges(n,keys=True,data=True)]

    return [ [e] + p for e in g.edges(n,keys=True,data=True)
                     for p in all_euler_paths( cr(g,e), e[1])]

def all_euler_paths_from_all_nodes( G):
   return [ p for n in G.nodes() for p in all_euler_paths( G, n)]

def all_euler_pair_paths_from_all_nodes( G0, G1):
   return [ pp for n0 in G0.nodes() for n1 in G1.nodes()
               for pp in all_euler_pair_paths( (G0, n0), (G1, n1))]


def gen_pair_graph( G0, G1):
   ns = sets.Set()
   es = []
   for e0 in G0.edges(keys=True,data=True):
      for e1 in G1.edges(keys=True,data=True):
         if True or e0[3]['label'] == e1[3]['label']:
            ns.add( (e0[0],e1[0]))
            ns.add( (e0[1],e1[1]))
            ns.add( (e0[0],e1[1]))
            ns.add( (e0[1],e1[0]))
            es.append( ((e0[0],e1[0]),(e0[1],e1[1]),(e0[2],e1[2]),(e0[3]['label'],e1[3]['label'])))
            es.append( ((e0[0],e1[1]),(e0[1],e1[0]),(e0[2],e1[2]),(e0[3]['label'],e1[3]['label'])))

   G = nx.MultiDiGraph()
   G.add_nodes_from( list(ns))
   for e in es:
      G.add_edge( e[0], e[1], key=e[2], label=(str(e[2])+"_"+str(e[3])))

   return G

class SatBasedEulerPathsRow:
   def __init__( self, p, row_nm):
      self.p = p
      self.row_nm = row_nm


   def sat_based_euler_paths_aux( self, G):
      m = self.p.ncols
#   
# Build raster of unflipped transistors
# Build raster of flipped   transistors
# Build raster of diffusions
#   
   
      self.node_values = G.nodes()
      print "node_values:", self.node_values


      edge_values = map( lambda e: e[2], G.edges(keys=True))

      print "edge_values:", edge_values


      self.unflipped = [ self.p.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('==>[%s]'%idx), edge_values)) for idx in range(0,m) ]
      self.flipped   = [ self.p.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('<==[%s]'%idx), edge_values)) for idx in range(0,m) ]

      self.diffs     = [ self.p.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('dif[%s]'%idx), self.node_values)) for idx in range(0,m+1) ]

      self.polys = [ self.p.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('ply[%s]'%idx), self.p.gate_values)) for idx in range(0,m) ]



#
# For each transistor, make sure that it is instantiated at least once
#
      for ev in edge_values:
         self.p.s.emit_exactly_one( map( lambda t: t.var(ev), self.unflipped + self.flipped))

      for e in G.edges(keys=True,data=True):
         n0 = e[0]
         n1 = e[1]
         k  = e[2]      
         g  = e[3]['label']

# unflipped         
#    '==>[idx]' == g implies diffs[idx] == n0 and diffs[idx+1] == n1
         for idx in range(0,m):
            self.p.s.emit_implies( self.unflipped[idx].var(k), self.diffs[idx  ].var(n0))
            self.p.s.emit_implies( self.unflipped[idx].var(k), self.diffs[idx+1].var(n1))
            self.p.s.emit_implies( self.unflipped[idx].var(k), self.polys[idx].var(g))
         
# flipped         
#    '<==[idx]' == g implies diffs[idx] == n1 and diffs[idx+1] == n0
            self.p.s.emit_implies( self.flipped[idx].var(k), self.diffs[idx  ].var(n1))
            self.p.s.emit_implies( self.flipped[idx].var(k), self.diffs[idx+1].var(n0))
            self.p.s.emit_implies( self.flipped[idx].var(k), self.polys[idx].var(g))

#
# For each transistor spot, determine if the diffusions are different
#
      self.different_diffs = [ self.p.s.add_var() for idx in range(0,m) ]
      self.same_diffs = [ self.p.s.add_var() for idx in range(0,m) ]
      self.different_diffs_and_unknown_tran = [ self.p.s.add_var() for idx in range(0,m) ]

      self.tran_defined = [ self.p.s.add_var() for idx in range(0,m) ]

      for idx in range(0,m):
         diff_pairs = []
         same_diff = []
         for (v0,v1) in zip( self.diffs[idx].vars, self.diffs[idx+1].vars):
            z = self.p.s.add_var()
            self.p.s.emit_or( [v0,v1], z)         
            diff_pairs.append( z)
            qq = self.p.s.add_var()
            self.p.s.emit_and( [v0,v1], qq)
            same_diff.append( qq)

         c1 = self.p.s.add_var()
         self.p.s.emit_tally( diff_pairs, [c1,self.different_diffs[idx]])

         self.p.s.emit_or( same_diff, self.same_diffs[idx])

         self.p.s.emit_or( self.unflipped[idx].vars + self.flipped[idx].vars, self.tran_defined[idx])

#
# OK: not c1 or same_diff 
# BAD: c2 or c1 and not same_diff
#

         q0 = self.p.s.add_var()
         self.p.s.emit_and( [c1, pysat.Sat.neg( self.same_diffs[idx])], q0)
         q1 = self.p.s.add_var()
         self.p.s.emit_or( [q0,self.different_diffs[idx]], q1)
         self.p.s.emit_and( [pysat.Sat.neg( self.tran_defined[idx]), q1], self.different_diffs_and_unknown_tran[idx])
            

#      self.count_different_diffs_and_unknown_tran = [ self.p.s.add_var() for idx in range(0,m) ]
#      self.p.s.emit_tally( self.different_diffs_and_unknown_tran, self.count_different_diffs_and_unknown_tran)



class SatBasedEulerPaths:
   def __init__( self):
      self.s   = pysat.Sat()
      self.mgr = pysat.VarMgr( self.s)
      self.ncols = 0
      self.extra_cols = 0
      self.limit_different_polys = 0
      self.limit_channel_width = -1

   def check_that_edge_keys_are_unique( self, G):
      """
Check that each edge of the Multigraph G has a unique key
"""
      tbl = {}
      for ( e0, e1, k, l) in G.edges( keys=True, data=True):
         assert k not in tbl
         tbl[k] = True

   def sat_based_euler_paths( self, GP, GN):
      self.check_that_edge_keys_are_unique( GP)
      self.check_that_edge_keys_are_unique( GN)

      self.ncols = max( GP.number_of_edges(), GN.number_of_edges()) + self.extra_cols

      self.gate_values = list(set( \
         map( lambda e: e[3]['label'], GP.edges(keys=True,data=True)) +
         map( lambda e: e[3]['label'], GN.edges(keys=True,data=True))))

      self.row_p = SatBasedEulerPathsRow( self, 'P-')
      self.row_p.sat_based_euler_paths_aux( GP)

      self.row_n = SatBasedEulerPathsRow( self, 'N-')
      self.row_n.sat_based_euler_paths_aux( GN)

#
# No more than one name per gate
#
      self.different_polys = []
      self.same_polys = []

      for (p,n) in zip( self.row_p.polys, self.row_n.polys):
         same_poly = [] 
         pn_poly = [] 
         for (pp,nn) in zip( p.vars, n.vars):
            zz = self.s.add_var()
            self.s.emit_or( [pp,nn], zz)
            pn_poly.append( zz)
            qq = self.s.add_var()
            self.s.emit_and( [pp,nn], qq)
            same_poly.append( qq)
      
         c1 = self.s.add_var()
         c2 = self.s.add_var()
         self.s.emit_tally( pn_poly, [c1,c2])
         self.different_polys.append( c2)
         z = self.s.add_var()
         self.s.emit_or( same_poly, z)
         self.same_polys.append( z)

      d = [ self.s.add_var() for p in self.different_polys ]

      self.s.emit_tally( self.different_polys, d)
      if self.limit_different_polys in range(len(self.different_polys)):
        self.s.emit_never( d[self.limit_different_polys])

      if self.limit_channel_width >= 0:
         self.emit_channel_constraints()

#
# p and n diffusions same
#
      self.same_p_and_n_diffusions = []
      self.different_p_and_n_diffusions = []

      for (p,n) in zip( self.row_p.diffs, self.row_n.diffs):
         same_diff = [] 

         p_dict = dict( zip( p.vals, p.vars))

         print "same_p_and_n_diffusions:", zip( p.vals, p.vars), zip( n.vals, n.vars)

         for (nval,nvar) in zip( n.vals, n.vars):
            if nval in p_dict:
               print "Match:", nval          
               same_diff.append( self.s.add_var())
               self.s.emit_and( [p_dict[nval],nvar], same_diff[-1])

         self.same_p_and_n_diffusions.append( self.s.add_var())
         print "defining same_p_and_n_diffusions:", same_diff, self.same_p_and_n_diffusions[-1]
         self.s.emit_or( same_diff, self.same_p_and_n_diffusions[-1])



#
# Build left and channel scans
#
#
# Determine nets
#
   def emit_channel_constraints( self):

      self.all_net_values = list(set( self.gate_values + self.row_p.node_values + self.row_n.node_values))

      assert len(self.row_p.diffs) == len(self.row_n.diffs)
      assert len(self.row_p.diffs) == len(self.row_p.polys) + 1
      assert len(self.row_n.diffs) == len(self.row_n.polys) + 1

      m = len(self.row_p.diffs)

      left_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'ls[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]

      left_scan_in = []
      for idx in range(0,m):
         left_scan_in.append( [ self.row_p.diffs[idx], self.row_n.diffs[idx]])
         if idx < m-1:
            left_scan_in.append( [ self.row_p.polys[idx], self.row_n.polys[idx]])

      assert all( [ len(l) <= 2 for l in left_scan_in])

      self.build_scan( m, left_scan, left_scan_in)

      right_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'rs[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]
      right_scan.reverse()

      right_scan_in = [ l[:] for l in left_scan_in[:] ] # explicit deep copy
      right_scan_in.reverse()

      self.build_scan( m, right_scan, right_scan_in)

      right_scan.reverse()

      and_of_scans = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'as[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]

      for ((l,r),q) in zip( zip( left_scan, right_scan), and_of_scans):      
         for val in q.vals:
            self.s.emit_and( [ l.var( val), r.var( val)], q.var( val))

      for q in and_of_scans:
         outs = [ self.s.add_var() for idx in range(self.limit_channel_width+1)]
         self.s.emit_tally( [ vr for (vl,vr) in zip(q.vals,q.vars) if vl not in ['vss','vcc']], outs)
         self.s.emit_never( outs[-1])

   def solve( self):
      self.s.solve()
      if self.s.indicator == 'UNSAT':
         print 'UNSAT'
      else:     
         assert self.s.indicator == 'SAT'
         print 'SAT'

         for nm,v in sorted( self.mgr.nm_map.items()):
            pass
#            print '%s=%s'%(nm, v.val())

   def build_scan( self, m, scn, scn_in):
      for idx in range(0,m):
         l = scn_in[2*idx][:]
         if idx > 0:
            l.append( scn[2*idx-1])

         for (val,var) in zip( scn[2*idx].vals, scn[2*idx].vars):
            ll = [ e.var(val) for e in l if val in e.vals ]
            self.s.emit_or( ll, var)

         if idx < m-1:
            l = scn_in[2*idx+1][:]
            l.append( scn[2*idx])
            for (val,var) in zip( scn[2*idx+1].vals, scn[2*idx+1].vars):
               ll = [ e.var(val) for e in l if val in e.vals ]
               self.s.emit_or( ll, var)

class SatBasedTiledPlacement:
   def __init__( self, ncols, nrows, args):
      self.s   = pysat.Sat( args.use_picosat, args.use_eureka)
      self.mgr = pysat.VarMgr( self.s)
      self.ncols = ncols
      self.nrows = nrows
      self.device_map = {}
      self.nsols = args.nsols
      if self.nsols > 1:
         self.s.nsols = self.nsols
      self.limit_channel_width = args.limit_channel_width
      self.exclude_poly_triples = args.exclude_poly_triples
      self.exclude_tcn_triples = args.exclude_tcn_triples

   def build_scan( self, m, scn, scn_in, scn_init=None):
      for idx in range(0,m):
         l = scn_in[idx][:]
         if idx > 0:
            l.append( scn[idx-1])
         elif scn_init:
            l.append( scn_init)

         for (val,var) in zip( scn[idx].vals, scn[idx].vars):
            ll = [ e.var(val) for e in l if val in e.vals ]
            self.s.emit_or( ll, var)

   def emit_poly_channel_constraints( self, row):

      m = self.ncols

      left_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'poly[%d]_ls[%02d]'%(row,idx), self.gate_values)) for idx in range(m)]

      left_scan_in = []
      for idx in range(0,m):
         left_scan_in.append( [ self.polys[self.devIdx( idx, row)]])

      assert all( [ len(l) <= 2 for l in left_scan_in])

      self.build_scan( m, left_scan, left_scan_in)

      right_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'poly[%d]_rs[%02d]'%(row,idx), self.gate_values)) for idx in range(m)]
      right_scan.reverse()

      right_scan_in = [ l[:] for l in left_scan_in[:] ] # explicit deep copy
      right_scan_in.reverse()

      self.build_scan( m, right_scan, right_scan_in)

      right_scan.reverse()

      and_of_scans = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'poly[%d]_as[%02d]'%(row,idx), self.gate_values)) for idx in range(m)]

      for ((l,r),q) in zip( zip( left_scan, right_scan), and_of_scans):      
         for val in q.vals:
            self.s.emit_and( [ l.var( val), r.var( val)], q.var( val))

      for q in and_of_scans:
         outs = [ self.s.add_var() for idx in range(self.limit_channel_width+1)]
         self.s.emit_tally( [ vr for (vl,vr) in zip(q.vals,q.vars) if vl not in []], outs)
         self.s.emit_never( outs[-1])

   def emit_diff_channel_constraints( self, row):

      m = self.ncols

      left_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'diff[%d]_ls[%02d]'%(row,idx), self.node_values)) for idx in range(m)]

      left_scan_in = []
      for idx in range(0,m):
         left_scan_in.append( [ self.diffs[self.diffIdx( idx, row)]])

      assert all( [ len(l) <= 2 for l in left_scan_in])

#      self.build_scan( m, left_scan, left_scan_in, self.diff_vcc_on)
      self.build_scan( m, left_scan, left_scan_in)

      right_scan = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'diff[%d]_rs[%02d]'%(row,idx), self.node_values)) for idx in range(m)]
      right_scan.reverse()

      right_scan_in = [ l[:] for l in left_scan_in[:] ] # explicit deep copy
      right_scan_in.reverse()

#      self.build_scan( m, right_scan, right_scan_in, self.diff_vss_on)
      self.build_scan( m, right_scan, right_scan_in)

      right_scan.reverse()

      and_of_scans = [ self.mgr.add_var( pysat.PowerSetEnumVar( self.s, 'diff[%d]_as[%02d]'%(row,idx), self.node_values)) for idx in range(m)]

      for ((l,r),q) in zip( zip( left_scan, right_scan), and_of_scans):      
         for val in q.vals:
            self.s.emit_and( [ l.var( val), r.var( val)], q.var( val))

      for q in and_of_scans:
         outs = [ self.s.add_var() for idx in range(self.limit_channel_width+1)]
         self.s.emit_tally( [ vr for (vl,vr) in zip(q.vals,q.vars) if vl not in []], outs)
         self.s.emit_never( outs[-1])

   def check_that_edge_keys_are_unique( self, G):
      """
Check that each edge of the Multigraph G has a unique key
"""
      tbl = {}
      for ( e0, e1, k, l) in G.edges( keys=True, data=True):
         assert k not in tbl
         tbl[k] = True

   def diffIdx( self, x, y):
      return (self.nrows+1)*x + y
   def devIdx( self, x, y):
      return self.nrows*x + y

   def invDevIdx( self, idx):
      return divmod( idx, self.nrows)
   def invDiffIdx( self, idx):
      return divmod( idx, self.nrows+1)

   def prevent_horizontal_mirror( self):
      pdevs = [ k for (k,(ty,e)) in self.device_map.items() if ty == 'p']
      if len(pdevs) > 1:
         for y in range( self.nrows-1,-1,-1):
             for x in range( self.ncols):
                idx   = self.devIdx( x, y)
                if self.nrows % 2 == 0:
                   if y < self.nrows/2:
                      print 'excluding', pdevs[0], 'from position', x, y
                      self.s.emit_never( self.flipped[idx].var(pdevs[0]))
                      self.s.emit_never( self.unflipped[idx].var(pdevs[0]))

   def build( self, GP, GN, sch):
      self.check_that_edge_keys_are_unique( GP)
      self.check_that_edge_keys_are_unique( GN)

      for e in GP.edges(keys=True,data=True):
         assert e[2] not in self.device_map
         self.device_map[e[2]] = ('p',e)

      for e in GN.edges(keys=True,data=True):
         assert e[2] not in self.device_map
         self.device_map[e[2]] = ('n',e)

      self.node_values = list(set(GP.nodes() + GN.nodes()))
      print "node_values:", self.node_values

      self.edge_values = [ e[2] for e in GP.edges(keys=True)] + [ e[2] for e in GN.edges(keys=True)]
      print "edge_values:", self.edge_values
      print "# of devices:", len(self.edge_values)

      self.gate_values = list(set( \
         map( lambda e: e[3]['label'], GP.edges(keys=True,data=True)) +
         map( lambda e: e[3]['label'], GN.edges(keys=True,data=True))))
      print "gate_values:", self.gate_values

      self.unflipped = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('nrm_%d_%d'%(x,y)), self.edge_values)) for x in range(self.ncols) for y in range(self.nrows) ]
#      print 'unflipped:', self.unflipped

      self.flipped   = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('flp_%d_%d'%(x,y)), self.edge_values)) for x in range(self.ncols) for y in range(self.nrows) ]
#      print 'flipped:', self.flipped

      self.pdev = [ self.s.add_var() for x in range(self.ncols) for y in range(self.nrows) ]
      self.ndev = [ self.s.add_var() for x in range(self.ncols) for y in range(self.nrows) ]
#      print self.ndev, self.pdev

      self.dev = [ self.mgr.add_var( pysat.BitVar( self.s, 'dev_%d_%d'%(x,y))) for x in range(self.ncols) for y in range(self.nrows) ]

#
# Uses diff indexing
#
      self.double_dev = [ self.mgr.add_var( pysat.BitVar( self.s, 'double_dev_%d_%d'%(x,y))) for x in range(self.ncols) for y in range(self.nrows+1) ]

#
# diffs have more rows
#
      self.diffs     = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('dif_%d_%d'%(x,y)), self.node_values)) for x in range(self.ncols) for y in range(self.nrows+1) ]

      self.double_diffs = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('double_diffs_%d_%d'%(x,y)), self.node_values)) for x in range(self.ncols) for y in range(self.nrows+1) ]

      self.non_double_diffs = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('non_double_diffs_%d_%d'%(x,y)), self.node_values)) for x in range(self.ncols) for y in range(self.nrows+1) ]

#      print 'diffs:', self.diffs

      self.polys     = [ self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('ply_%d_%d'%(x,y)), self.gate_values)) for x in range(self.ncols) for y in range(self.nrows) ]

#      print 'polys:', self.polys

      self.diff_vcc_on = self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('diff_vcc_on'), self.node_values))
      self.diff_vss_on = self.mgr.add_var( pysat.PossiblyUnknownEnumVar( self.s, ('diff_vss_on'), self.node_values))

      self.s.emit_always( self.diff_vcc_on.var('vcc')) 
      self.s.emit_always( self.diff_vss_on.var('vss')) 

      self.prevent_horizontal_mirror()

      for y in range( self.nrows-1,-1,-1):
          for x in range( self.ncols):
             idx  = self.devIdx( x, y)
             self.s.emit_or( [ self.pdev[idx], self.ndev[idx]], self.dev[idx].var())

      for y in range( self.nrows,-1,-1):
          for x in range( self.ncols):
             didx  = self.diffIdx( x, y)

             if y == self.nrows or y == 0:
                self.s.emit_never( self.double_dev[didx].var())
             else:
                idx   = self.devIdx( x, y)
                idxm1 = self.devIdx( x, y-1)
                self.s.emit_and( [ self.dev[idxm1].var(), self.dev[idx].var()], self.double_dev[didx].var())


#
# If multiple solutions are desired,
#    then add placement variables to the important variable list
#
      if self.nsols > 1:
         self.s.important_vars = []
         for ev in self.edge_values:
            ivs = [ x.var(ev) for x in self.unflipped + self.flipped]
            self.s.important_vars += ivs

#
# For each transistor, make sure that it is instantiated at exactly once
#
      for ev in self.edge_values:
         ivs = [ x.var(ev) for x in self.unflipped + self.flipped]
         self.s.emit_exactly_one( ivs)

      valences = {}
      for e in GN.edges(keys=True,data=True) + GP.edges(keys=True,data=True):
         n0 = e[0]
         n1 = e[1]
         k  = e[2]      
         g  = e[3]['label']
         if n0 not in valences: valences[n0] = 0
         valences[n0] += 1
         if n1 not in valences: valences[n1] = 0
         valences[n1] += 1         
         if g  not in valences: valences[g]  = 0
         valences[g] += 1         

#
# Add in a connection for each port
#
      for pin in sch.inputs + sch.outputs + sch.ioputs:
         if pin not in valences: valences[pin] = 0
         valences[pin] += 1

      for (k,v) in valences.items():
         print "Valance", k, v

      p_evs = [ ev for ev in self.edge_values if self.device_map[ev][0] == 'p']
      n_evs = [ ev for ev in self.edge_values if self.device_map[ev][0] == 'n']


      for y in range( self.nrows-1,-1,-1):
         for x in range( self.ncols):
            idx   = self.devIdx( x, y)

            p_vars = [ self.unflipped[idx].var(ev) for ev in p_evs] + [ self.flipped[idx].var(ev) for ev in p_evs]
            n_vars = [ self.unflipped[idx].var(ev) for ev in n_evs] + [ self.flipped[idx].var(ev) for ev in n_evs]

            self.s.emit_or( p_vars, self.pdev[idx])
            self.s.emit_or( n_vars, self.ndev[idx])

      for e in GN.edges(keys=True,data=True) + GP.edges(keys=True,data=True):
         n0 = e[0]
         n1 = e[1]
         k  = e[2]      
         g  = e[3]['label']

         for y in range( self.nrows-1,-1,-1):
             for x in range( self.ncols):

                didx  = self.diffIdx( x, y)
                didx1 = self.diffIdx( x, y+1)
                idx   = self.devIdx( x, y)

# unflipped         
#    '==>[idx]' == g implies diffs[idx] == n0 and diffs[idx+1] == n1
                self.s.emit_implies( self.unflipped[idx].var(k), self.diffs[didx ].var(n0))
                self.s.emit_implies( self.unflipped[idx].var(k), self.diffs[didx1].var(n1))
                self.s.emit_implies( self.unflipped[idx].var(k), self.polys[idx ].var(g))
         
# flipped         
#    '<==[idx]' == g implies diffs[idx] == n1 and diffs[idx+1] == n0
                self.s.emit_implies( self.flipped[idx].var(k), self.diffs[didx ].var(n1))
                self.s.emit_implies( self.flipped[idx].var(k), self.diffs[didx1].var(n0))
                self.s.emit_implies( self.flipped[idx].var(k), self.polys[idx ].var(g))

      for nv in self.node_values:
         for y in range( self.nrows,-1,-1):
             for x in range( self.ncols):
                didx  = self.diffIdx( x, y)
                if valences[nv] == 2:
                    self.s.emit_and( [ self.diffs[didx].var(nv), self.double_dev[didx].var()], self.double_diffs[didx].var(nv))
                else:
                    self.s.emit_never( self.double_diffs[didx].var(nv))

                self.s.emit_and( [ pysat.Sat.neg( self.double_diffs[didx].var(nv)), self.diffs[didx].var(nv)], self.non_double_diffs[didx].var(nv))

#
# Old PPNN cols arch
#
      if False:
          for y in range( self.nrows-1,-1,-1):
              for x in range( self.ncols):
                 idx   = self.devIdx( x, y)
                 if x < self.ncols/2:
                    print 'no n', x, y 
                    self.s.emit_never( self.ndev[idx])
                 if x >= (self.ncols+1)/2:
                    print 'no p', x, y 
                    self.s.emit_never( self.pdev[idx])

      if True:
          assert self.ncols == 4 or self.ncols == 2
          for y in range( self.nrows-1,-1,-1):
             for x in range( self.ncols):
                idx   = self.devIdx( x, y)
                if x in [1,2]:
                   print 'no n', x, y 
                   self.s.emit_never( self.ndev[idx])
                if x in [0,3]:
                   print 'no p', x, y 
                   self.s.emit_never( self.pdev[idx])


      for y in range( self.nrows-1,-1,-1):
          for x in range( self.ncols):
             if y > 0:
                idx   = self.devIdx( x, y)
                idxm1 = self.devIdx( x, y-1)

                if True:
#
# ./euler.py -tiled_placer -nrows 4 -ncols 3 c04ltn10fn0a5.sch
# Fails in 10s
#
                   self.s.emit_at_most_one( [self.pdev[idx], self.ndev[idxm1]])
                   self.s.emit_at_most_one( [self.ndev[idx], self.pdev[idxm1]])
                   continue

                for (e_n, v) in self.device_map.items():
                    print e_n, v
                    if v[0] != 'n': continue
                    for (e_p, v) in self.device_map.items():
                        print e_p, v
                        if v[0] != 'p': continue 

                        if False:

#
# ./euler.py -tiled_placer -nrows 4 -ncols 3 c04ltn10fn0a5.sch
# Fails in 10s
#
                           has_n = self.s.add_var()
                           has_p = self.s.add_var()

                           self.s.emit_or( [ self.unflipped[idx].var( e_n),
                                             self.unflipped[idxm1].var( e_n),
                                             self.flipped[idx].var( e_n),
                                             self.flipped[idxm1].var( e_n)], has_n)

                           self.s.emit_or( [ self.unflipped[idx].var( e_p),
                                             self.unflipped[idxm1].var( e_p),
                                             self.flipped[idx].var( e_p),
                                             self.flipped[idxm1].var( e_p)], has_p)

                           self.s.emit_at_most_one( [has_n, has_p])

                        if False:
#
# ./euler.py -tiled_placer -nrows 4 -ncols 3 c04ltn10fn0a5.sch
# Fails in 23s
#
                           self.s.emit_at_most_one( [ self.unflipped[idx].var( e_n), \
                                                      self.unflipped[idx].var( e_p), \
                                                      self.unflipped[idxm1].var( e_p), \
                                                      self.unflipped[idxm1].var( e_n), \
                                                      self.flipped[idx].var( e_n), \
                                                      self.flipped[idx].var( e_p), \
                                                      self.flipped[idxm1].var( e_n), \
                                                      self.flipped[idxm1].var( e_p)])

#
# Assume horizontal poly:
#    if we have a triple of polys named (X,Y,Z), then if Y is valid, then (X valid => X = Y or Z valid => X = Z) 
#    This is the same as: ~ vald Y or ~ valid X or ~ valid Z or X=Y or Z=Y
#     
      if self.exclude_poly_triples:
       print "Added constraints for blocked poly..."            
       for y in range( self.nrows):
          for x in range( self.ncols-2):
              idx0   = self.devIdx( x+0, y)
              idx1   = self.devIdx( x+1, y)
              idx2   = self.devIdx( x+2, y)

              valid0 = self.s.add_var()
              valid1 = self.s.add_var()
              valid2 = self.s.add_var()

              self.s.emit_or( self.polys[idx0].vars, valid0)
              self.s.emit_or( self.polys[idx1].vars, valid1)
              self.s.emit_or( self.polys[idx2].vars, valid2)

              eq01 = [ self.s.add_var() for g in self.gate_values]
              for (g,a) in zip( self.gate_values, eq01):
                 self.s.emit_and( [ self.polys[idx0].var(g), self.polys[idx1].var(g)], a)

              eq12 = [ self.s.add_var() for g in self.gate_values]
              for (g,a) in zip( self.gate_values, eq12):
                 self.s.emit_and( [ self.polys[idx1].var(g), self.polys[idx2].var(g)], a)

              or01 = self.s.add_var()
              or12 = self.s.add_var()

              self.s.emit_or( eq01, or01)        
              self.s.emit_or( eq12, or12)        

              self.s.add_clause( [ pysat.Sat.neg( valid0), pysat.Sat.neg( valid1), pysat.Sat.neg( valid2), or01, or12])



#
# Assume horizontal tcn:
#    if we have a triple of tcns named (X,Y,Z), then if Y is valid, then (X valid => X = Y or Z valid => X = Z) 
#    This is the same as: ~ vald Y or ~ valid X or ~ valid Z or X=Y or Z=Y
#     
      if self.exclude_tcn_triples:
       print "Added constraints for blocked tcn..."            
       for y in range( self.nrows+1):
          for x in range( self.ncols-2):
              idx0   = self.diffIdx( x+0, y)
              idx1   = self.diffIdx( x+1, y)
              idx2   = self.diffIdx( x+2, y)

              valid0 = self.s.add_var()
              valid1 = self.s.add_var()
              valid2 = self.s.add_var()

              if False:
#
# Original run. Seems to be too restrictive: yields 109 ltn10
#
                 self.s.emit_or( self.diffs[idx0].vars, valid0)
                 self.s.emit_or( self.diffs[idx1].vars, valid1)
                 self.s.emit_or( self.diffs[idx2].vars, valid2)
              else:
#
# New rule: yields 2871 ltn10
#
                 self.s.emit_or( self.non_double_diffs[idx0].vars, valid0)
                 self.s.emit_or( self.non_double_diffs[idx1].vars, valid1)
                 self.s.emit_or( self.non_double_diffs[idx2].vars, valid2)

              eq01 = [ self.s.add_var() for g in self.node_values]
              for (g,a) in zip( self.node_values, eq01):
                 self.s.emit_and( [ self.diffs[idx0].var(g), self.diffs[idx1].var(g)], a)

              eq12 = [ self.s.add_var() for g in self.node_values]
              for (g,a) in zip( self.node_values, eq12):
                 self.s.emit_and( [ self.diffs[idx1].var(g), self.diffs[idx2].var(g)], a)

              print x, y, eq01, eq12

              or01 = self.s.add_var()
              or12 = self.s.add_var()

              self.s.emit_or( eq01, or01)        
              self.s.emit_or( eq12, or12)        

              self.s.add_clause( [ pysat.Sat.neg( valid0), pysat.Sat.neg( valid1), pysat.Sat.neg( valid2), or01, or12])


   def solve( self):
      self.s.solve()
      if self.s.indicator == 'UNSAT':
         print 'UNSAT'
      else:     
         assert self.s.indicator == 'SAT'
         print 'SAT'

         for nm,v in sorted( self.mgr.nm_map.items()):
            pass
#            print '%s=%s'%(nm, v.val())


   def extract_device_placement_iv( self, important_variable_model):
      for e in GN.edges(keys=True,data=True) + GP.edges(keys=True,data=True):
         n0 = e[0]
         n1 = e[1]
         k  = e[2]      
         g  = e[3]['label']


      device_placement = {}

      i = 0
      for ev in self.edge_values:
         ivs_unflipped = [ ( idx, x.var(ev)) for (idx,x) in enumerate( self.unflipped)]
         vals = important_variable_model[ i: i+len(ivs_unflipped)]     

         for ( (idx,var), val) in zip( ivs_unflipped, vals):
            if val == 1:
               ( x, y) = self.invDevIdx( idx)
               device_placement[ev] = ( x, y, 'd')

         i += len(ivs_unflipped)

         ivs_flipped   = [ ( idx, x.var(ev)) for (idx,x) in enumerate( self.flipped)]
         vals = important_variable_model[ i: i+len(ivs_flipped)]     

         for ( (idx,var), val) in zip( ivs_flipped, vals):
            if val == 1:
               ( x, y) = self.invDevIdx( idx)
               device_placement[ev] = ( x, y, 'i')

         i += len(ivs_flipped)

      for ev in self.edge_values:
         assert ev in device_placement

      return device_placement   

class SatPartitionAux:
   def __init__( self, dad, ty, G):
      self.dad = dad
      self.ty = ty
      self.G = G
      self.edges = G.edges( keys=True, data=True)
      self.vars = [ self.dad.mgr.add_var( pysat.BitVar( self.dad.s, ('%s_edge_%d' % (ty,idx)))) for (idx,e) in enumerate(self.edges)]
      self.semantic()

   def semantic( self):
      """
Count the number nets that touch a device with both p_var=off and p_var=on
"""
# foreach net, find all the devices, construct predicate both on and off, form a tally      

      for (idx,e) in enumerate(self.edges):
         ( diff0, diff1, k, lbl) = e
         for nm in [diff0, diff1, lbl['label']]:
            if nm not in self.dad.nets:
               self.dad.nets[nm] = []
            self.dad.nets[nm].append( (self.ty,idx))

#      print nets

      n = len(self.edges)
      out_vars = [ self.dad.s.add_var() for idx in range(n+1)]

      self.dad.s.emit_tally( map( lambda v: v.var(), self.vars), out_vars)
      
      if n % 4 == 2:
         assert n >= 2
         limit = n/2 + 1 
         print "Limiting number of devices in %s master to %d of %d" % (self.ty, limit, n)
         self.dad.s.emit_always( out_vars[limit-1])
         self.dad.s.emit_never( out_vars[limit])
      else:
         assert n >= 2
         limit = n/2
         print "Limiting number of devices in %s master to %d of %d" % (self.ty, limit, n)
         self.dad.s.emit_always( out_vars[limit-1])
         self.dad.s.emit_never( out_vars[limit])

   def split( self, mdl=None):
      G0 = nx.MultiDiGraph()
      G1 = nx.MultiDiGraph()

      if mdl:
         iv_m = dict( zip( self.dad.s.important_vars, mdl))

         m = {}
         for v in self.vars:
             assert v.var() in iv_m
             m[v] = iv_m[v.var()]

      else:
         m = dict( [ (v,v.val()) for v in self.vars])

      for ( tuple, var) in zip( self.edges, self.vars):
         ( e0, e1, k, lbl) = tuple
         if m[var]:
            G1.add_edge( e0, e1, key=k, label=lbl['label'])         
         else:   
            G0.add_edge( e0, e1, key=k, label=lbl['label'])         

      return (G0,G1)



class SatPartition:
   def __init__( self, GP, GN, args):
      """
Divide (GP,GN) into two graphs each, without about half the device (edges) in each graph, minimizing the number of wires that cross 
"""
      self.s   = pysat.Sat( args.use_picosat, args.use_eureka)
      self.mgr = pysat.VarMgr( self.s)
      self.limit_crossings = args.limit_crossings
      self.all_sat = args.all_sat
      self.nsols = args.nsols
      if self.nsols > 1:
         self.s.nsols = self.nsols

      self.nets = {}
      self.p_row = SatPartitionAux( self, 'p', GP)
      self.n_row = SatPartitionAux( self, 'n', GN)

      self.semantic()


   def print_model( self):

      if self.s.indicator == 'SAT':
         
         in_common = {}
         only_in_off = {}
         only_in_on = {}

         for ( (k, v), net_var) in zip( self.lst, self.net_vars):
            if k in ['vss','vcc']:
               in_common[k] = True
               print 'rail', net_var
            elif net_var.val():
               in_common[k] = True
               print 'crossing', net_var
            else:
               print 'no crossing', net_var
               for ( ty, idx) in v:
                  if   ty == 'p':
                     vv = self.p_row.vars[idx].val()
                  elif ty == 'n':
                     vv = self.n_row.vars[idx].val()
                  else:
                     assert False
                  if vv:
                     only_in_on[k] = True   
                  else:
                     only_in_off[k] = True   

            for ( ty, idx) in v:
               if   ty == 'p':
                  vv = self.p_row.vars[idx].val()
               elif ty == 'n':
                  vv = self.n_row.vars[idx].val()
               else:
                  assert False
               print '   ', ty, idx, vv


         print 'Nets in common:', in_common.keys()
         print 'Nets in master:', only_in_on.keys()
         print 'Nets in slave:', only_in_off.keys()

         for nm,v in sorted( self.mgr.nm_map.items()):
            pass
#            print '%s=%s'%(nm, v.val())


   def semantic( self):
      self.lst = [ (k, sets.Set( v)) for ( k, v) in self.nets.items()]

      self.net_vars = [ self.mgr.add_var( pysat.BitVar( self.s, ('net_%s' % k))) for (k, v) in self.lst]

      for ( (k, v), net_var) in zip(self.lst,self.net_vars):
         if k in ['vss','vcc']: continue

#
# Net all in group 0
#     all_false
# Net all in group 1
#     all true
# Otherwise
#     a mix; some one, and some off
#

         one_off = self.s.add_var()
         one_on  = self.s.add_var()

         self.s.emit_and( [one_off, one_on], net_var.var())

         or_on_vars = []
         or_off_vars = []

         for ( ty, idx) in v:
            if   ty == 'p':
               vv = self.p_row.vars[idx].var()
            elif ty == 'n':
               vv = self.n_row.vars[idx].var()
            else:
               assert False
            or_on_vars.append( vv)             
            or_off_vars.append( pysat.Sat.neg( vv))

         self.s.emit_or( or_on_vars, one_on)
         self.s.emit_or( or_off_vars, one_off)

      out_vars = [ self.s.add_var() for idx in range( self.limit_crossings+1)]

      self.s.emit_tally( [ v.var() for v in self.net_vars], out_vars)
      self.s.emit_never( out_vars[-1])

      if self.all_sat:
         self.s.important_vars = [ v.var() for v in self.p_row.vars] + [ v.var() for v in self.n_row.vars]
         self.s.solve()

         for ( idx, mdl) in enumerate( self.s.all_models):
            if idx > 0:
               print 32*'='
            print "Model:", idx

            (GP0,GP1) = self.p_row.split( mdl)
            (GN0,GN1) = self.n_row.split( mdl)

            print '|P0|:', len(GP0.edges(keys=True,data=True))
            print '|N0|:', len(GN0.edges(keys=True,data=True))
            print '|P1|:', len(GP1.edges(keys=True,data=True))
            print '|N1|:', len(GN1.edges(keys=True,data=True))

            master = [ e[2] for e in GP0.edges(keys=True,data=True) + GN0.edges(keys=True,data=True)]
            slave  = [ e[2] for e in GP1.edges(keys=True,data=True) + GN1.edges(keys=True,data=True)]

            print "Option name=placement_group_dependency master=%s slave=%s" % ( ','.join( master), ','.join( slave))


      else:
         self.s.solve()
         self.print_model()



class LatchFabric14nm:
#
# 0 1 2 3 4 5 6 0 1 2 3 4 5 6 0 1 2 3 4 5 6 
#  0 1 2 3 4 5 6 0 1 2 3 4 5 6 0 1 2 3 4 5 
# *|*|*|*|*|*|*+*|*|*|*|*|*|*+*|*|*|*|*|*|*
#
# 7*chunks   = # of diffs
# 7*chunks-1 = # of devices
# idx % 7 in [0,1,4,5] straight through
# idx % 7 in [6] never used
#


  def __init__( self, GP, GN, limit_channel_width, extra_units, blank_half_cell):
     ncols = max( GP.number_of_edges(), GN.number_of_edges())
     chunks = (ncols + 5)//6
     chunks += extra_units
     target_ncols = 7*chunks - 1
     self.sbep = SatBasedEulerPaths()
     self.sbep.limit_channel_width = limit_channel_width
     self.sbep.blank_half_cell = blank_half_cell
     self.sbep.extra_cols = target_ncols - ncols
     self.sbep.limit_different_polys = -1

     self.sbep.sat_based_euler_paths( GP, GN)

     for idx in range(0,target_ncols):
         if self.sbep.blank_half_cell and idx in [0,1,2]:
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_p.unflipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_p.flipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_n.unflipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_n.flipped[idx].vars]

         if idx % 7 in [0,1,4,5]:
            self.sbep.s.emit_always( self.sbep.same_polys[idx])
            self.sbep.s.emit_never( self.sbep.different_polys[idx])
         if idx % 7 in [6]:
            z = self.sbep.s.add_var()
            self.sbep.s.emit_or( self.sbep.row_p.unflipped[idx].vars + \
                                 self.sbep.row_p.flipped[idx].vars, z)
            self.sbep.s.emit_never( z)
            z = self.sbep.s.add_var()
            self.sbep.s.emit_or( self.sbep.row_n.unflipped[idx].vars + \
                                 self.sbep.row_n.flipped[idx].vars, z)
            self.sbep.s.emit_never( z)

#      self.count_different_diffs_and_unknown_tran = [ self.p.s.add_var() for idx in range(0,m) ]
     all_diffs = []
     for idx in range(0,target_ncols):
         if idx % 7 not in [6]:
            all_diffs.append( self.sbep.row_p.different_diffs_and_unknown_tran[idx])
            all_diffs.append( self.sbep.row_n.different_diffs_and_unknown_tran[idx])

     limit_all_diffs = 0
     count_all_diffs = [ self.sbep.s.add_var() for i in range(limit_all_diffs+1)]
     self.sbep.s.emit_tally( all_diffs, count_all_diffs)
     self.sbep.s.emit_never( count_all_diffs[limit_all_diffs])


  def solve( self):
     self.sbep.solve()

  def report( self):
     if self.sbep.s.indicator == 'UNSAT':
        return
     for idx in range(self.sbep.ncols+1):
        print "  ", self.sbep.row_p.diffs[idx].val(), self.sbep.row_n.diffs[idx].val()
        if idx < self.sbep.ncols:
            def gp( row, idx):
               unflp = row.unflipped[idx].val()
               flp   = row.flipped[idx].val()
               return (unflp if unflp != '<UNKNOWN>' else flp, row.polys[idx].val())

            print "{%s}%s"%gp(self.sbep.row_p, idx), "{%s}%s"%gp(self.sbep.row_n, idx)

  def fancy_report( self, fp):
     if self.sbep.s.indicator == 'UNSAT':
        return

     m = self.sbep.ncols+1

     assert m % 7 == 0

#
# 0|1|2|3|4|5|6|0|
#  0 1 2 3 4 5 6 0
#
     def tr( nm):
        return 'syn0' if nm == '<UNKNOWN>' else nm
     def t_exists( row, idx):
        unflp = row.unflipped[idx].val()
        flp   = row.flipped[idx].val()
        res = unflp != '<UNKNOWN>' or flp != '<UNKNOWN>'
        print 't_exists', idx, unflp, flp, res

        return res

     for idx in range(m):
        if idx % 7 == 0:
            fp.write( u"  u = c.addUnit()\n")

        fp.write( u"  u.addSD( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
#
# Stutter
#
        if idx % 7 == 3:
            fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
            fp.write( u"  u.addSD( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
        if idx < self.sbep.ncols:
            if idx % 7 == 6: # border between cells
               pass
            elif (idx % 7) in [0,1,4,5]:
               either_exists = t_exists( self.sbep.row_p, idx) or t_exists( self.sbep.row_n, idx)
               p_poly = tr(self.sbep.row_p.polys[idx].val()) if either_exists else 'syn0'
               n_poly = tr(self.sbep.row_n.polys[idx].val()) if either_exists else 'syn0'
               fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( p_poly, n_poly))
            else:
               p_exists = t_exists( self.sbep.row_p, idx)
               n_exists = t_exists( self.sbep.row_n, idx)
               p_poly = tr(self.sbep.row_p.polys[idx].val()) if p_exists else 'syn0'
               n_poly = tr(self.sbep.row_n.polys[idx].val()) if n_exists else 'syn0'
               fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( p_poly, n_poly))

class LatchFabric10nm:
#
# 0 1 2 3 4 5 6 0 1 2 3 4 5 6 0 1 2 3 4 5 6 
#  0 1 2 3 4 5 6 0 1 2 3 4 5 6 0 1 2 3 4 5 
# *|*|*|*|*|*|*+*|*|*|*|*|*|*+*|*|*|*|*|*|*
#
# 7*chunks   = # of diffs
# 7*chunks-1 = # of devices
# idx % 7 in [0,1,4,5] straight through
# idx % 7 in [6] never used
#


  def __init__( self, GP, GN, limit_channel_width, extra_units, blank_half_cell):
     ncols = max( GP.number_of_edges(), GN.number_of_edges())
     chunks = (ncols + 5)//6
     chunks += extra_units
     target_ncols = 7*chunks - 1
     self.sbep = SatBasedEulerPaths()
     self.sbep.limit_channel_width = limit_channel_width
     self.sbep.blank_half_cell = blank_half_cell
     self.sbep.extra_cols = target_ncols - ncols
     self.sbep.limit_different_polys = -1

     self.sbep.sat_based_euler_paths( GP, GN)

     for idx in range(0,target_ncols):
         if (self.sbep.blank_half_cell and idx in [0,1,2]) or (idx % 7 in [6]):
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_p.unflipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_p.flipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_n.unflipped[idx].vars]
            [ self.sbep.s.emit_never( v) for v in self.sbep.row_n.flipped[idx].vars]

         if idx % 7 in [0,1,4,5]:
            self.sbep.s.emit_always( self.sbep.same_polys[idx])
            self.sbep.s.emit_never( self.sbep.different_polys[idx])

     all_diffs = []
     for idx in range(0,target_ncols):
         if idx % 7 not in [6]:
            all_diffs.append( self.sbep.row_p.different_diffs_and_unknown_tran[idx])
            all_diffs.append( self.sbep.row_n.different_diffs_and_unknown_tran[idx])

         if idx % 7 in [3]: # p and n diffusions should be the same; feature in 10nm fabric
            print "emit_always for shared diffusion"
            pass
#            self.sbep.s.emit_always( self.sbep.same_p_and_n_diffusions[idx])
#            self.sbep.s.emit_always( self.sbep.different_p_and_n_diffusions[idx])


     limit_all_diffs = 0
     count_all_diffs = [ self.sbep.s.add_var() for i in range(limit_all_diffs+1)]
     self.sbep.s.emit_tally( all_diffs, count_all_diffs)
     self.sbep.s.emit_never( count_all_diffs[limit_all_diffs])


  def solve( self):
     self.sbep.solve()

  def report( self):
     if self.sbep.s.indicator == 'UNSAT':
        return
     for idx in range(self.sbep.ncols+1):
        print "  ", self.sbep.row_p.diffs[idx].val(), self.sbep.row_n.diffs[idx].val()
        if idx < self.sbep.ncols:
            def gp( row, idx):
               unflp = row.unflipped[idx].val()
               flp   = row.flipped[idx].val()
               return (unflp if unflp != '<UNKNOWN>' else flp, row.polys[idx].val())

            print "{%s}%s"%gp(self.sbep.row_p, idx), "{%s}%s"%gp(self.sbep.row_n, idx)

  def fancy_report( self, fp):
     if self.sbep.s.indicator == 'UNSAT':
        return

     m = self.sbep.ncols+1

     assert m % 7 == 0

#
# 0|1|2|3|4|5|6|0|
#  0 1 2 3 4 5 6 0
#
     def tr( nm):
        return 'syn0' if nm == '<UNKNOWN>' else nm
     def t_exists( row, idx):
        unflp = row.unflipped[idx].val()
        flp   = row.flipped[idx].val()
        res = unflp != '<UNKNOWN>' or flp != '<UNKNOWN>'
        print 't_exists', idx, unflp, flp, res

        return res

     for idx in range(m):
        if idx % 7 == 0:
            fp.write( u"  u = c.addUnit()\n")

        fp.write( u"  u.addSD( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
#
# Stutter
#
        if idx % 7 == 3:
            fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
            fp.write( u"  u.addSD( \'%s\', \'%s\')\n" % ( tr(self.sbep.row_p.diffs[idx].val()), tr(self.sbep.row_n.diffs[idx].val())))
        if idx < self.sbep.ncols:
            if idx % 7 == 6: # border between cells
               pass
            elif (idx % 7) in [0,1,4,5]:
               either_exists = t_exists( self.sbep.row_p, idx) or t_exists( self.sbep.row_n, idx)
               p_poly = tr(self.sbep.row_p.polys[idx].val()) if either_exists else 'syn0'
               n_poly = tr(self.sbep.row_n.polys[idx].val()) if either_exists else 'syn0'
               fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( p_poly, n_poly))
            else:
               p_exists = t_exists( self.sbep.row_p, idx)
               n_exists = t_exists( self.sbep.row_n, idx)
               p_poly = tr(self.sbep.row_p.polys[idx].val()) if p_exists else 'syn0'
               n_poly = tr(self.sbep.row_n.polys[idx].val()) if n_exists else 'syn0'
               fp.write( u"  u.addPL( \'%s\', \'%s\')\n" % ( p_poly, n_poly))

def add_from_sch( sch):
  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

  for d in sch.devices:
     nm  = d.nm
     b   = d.terminals[u'b']
     sds = [d.terminals[u's'], d.terminals[u'd']]
     g   = d.terminals[u'g']
#     print d.ty, d.nm, sds[0], sds[1], g
     if   d.ty == 'p':
        GP.add_edge( sds[0], sds[1], key=nm, label=g)
     elif d.ty == 'n':
        GN.add_edge( sds[0], sds[1], key=nm, label=g)
     else: # pragma: no cover
       assert False
          
  return (GP,GN)  

def graph2png( G, name, fn):
  G.name = name
  nx.write_dot( G, fn + '.dot')
  graph = nx.to_agraph( G)
  graph.layout(prog='dot')
  os.system( "dot -Tpng -o " + fn + ".png " + fn + ".dot")

def draw_individual( fn, GP, GN):
  graph2png( GP, "P", fn + '-p')
  graph2png( GN, "N", fn + '-n')

def draw_pair_graph( fn, GP, GN):
  prodG = gen_pair_graph( GP, GN)
  graph2png( prodG, "prodG", fn + 'prod')

def print_all_chains( fn, GP, GN):
  def print_chain(a):
     for l in sorted(a):
        first = True
        for e in l:
            if first:
               print " %3s" % (e[0]),
               first = False
            print "={%s,%s}= %3s" % ( e[2], e[3]['label'], e[1]),
        print ""

  def same_gate( a, b):
    return all( map( lambda (x,y): x[3]['label'] == y[3]['label'], zip(a,b)))
    
  if True:
     p = all_euler_paths_from_all_nodes( GP)
     n = all_euler_paths_from_all_nodes( GN)
     pn = all_euler_pair_paths_from_all_nodes( GP, GN)

     print "P:"
     for a in p:
       print_chain([a])

     print "N:"
     for a in n:
       print_chain([a])


     print "Stitched:"
     for (a,b) in [ (a,b) for a in p for b in n if same_gate( a, b)]:
        print "Pair:"
        print_chain([a])
        print_chain([b])

     print "Simult:"
     for (a,b) in pn:
        print "Pair:"
        print_chain([a])
        print_chain([b])


def run( fn, GP, GN):
  print "Starting..."


  if True:
    sbep = SatBasedEulerPaths()
    sbep.sat_based_euler_paths( GP, GN)
    sbep.solve()
    return sbep

import threed
import route

def gen_threed_routing_problem( fn, GP, GN, args, sch):


  if not args.linta:
     sbep = SatBasedEulerPaths()
     sbep.extra_cols = args.extra_cols
     sbep.limit_different_polys = args.limit_different_polys

     sbep.sat_based_euler_paths( GP, GN)
     sbep.solve()

     if sbep.s.indicator == 'UNSAT':
       return

     m = len(sbep.row_p.unflipped)
     assert m == len(sbep.row_n.unflipped)
     assert m == len(sbep.row_p.flipped)
     assert m == len(sbep.row_n.flipped)

     def t_exists( row, idx):
       unflp = row.unflipped[idx].val()
       flp   = row.flipped[idx].val()
       res = unflp != '<UNKNOWN>' or flp != '<UNKNOWN>'
#       print 't_exists', idx, unflp, flp, res
       return res

     def tr( nm):
        return 'syn0' if nm == '<UNKNOWN>' else nm

     for idx in range(m+1):
        if False:
           p_diff = tr( sbep.row_p.diffs[idx].val())
           n_diff = tr( sbep.row_n.diffs[idx].val())

           print 'DIFF', p_diff, n_diff

           if idx < m:
              p_poly = tr( sbep.row_p.polys[idx].val())
              n_poly = tr( sbep.row_n.polys[idx].val())
              p_exists = t_exists( sbep.row_p, idx)
              n_exists = t_exists( sbep.row_n, idx)
              either_exists = p_exists or n_exists
              print 'POLY', p_poly, n_poly

     x_width = max( len( sbep.row_p.polys), len( sbep.row_n.polys))
  else:
     x_width = 1 + max( [d.x for d in sch.devices])



#
# For the "Regular" fabric, use height 5, ny
#
  fabric_nm = args.threed
  if   fabric_nm == 'Fabric3DReg':
     ( y_height, ny, py) = ( 4, 0, 1)
  elif fabric_nm == 'Fabric3DOld':
     ( y_height, ny, py) = ( 4, 0, 2)
  elif fabric_nm == 'Fabric3D':
     ( y_height, ny, py) = ( 5, 2, 2)
  else:
     assert False, fabric_nm

  fabric = threed.FabricFactory().build( fabric_nm, x_width, y_height)
  placement = route.Placement( fabric)
  placement.rails = ['vcc','vss']

  if sch != None:
     placement.inputs  = sch.inputs
     placement.outputs = sch.outputs
     placement.ioputs  = sch.ioputs
     placement.ports = sch.inputs + sch.outputs + sch.ioputs

  if not args.linta:
     for (ty,row,y) in [('p',sbep.row_p,py), ('n',sbep.row_n,ny)]:
        for idx in range(m):
           l = [tr( row.diffs[idx].val()), tr( row.polys[idx].val()), tr( row.diffs[idx+1].val()), ty]
           if l[1] == 'syn0':
             print '#   placement.add_device( Device( %s, %d, %s, 2))' % (', '.join( map( lambda n: ("'%s'" % n), l)),idx,ty+'y')
           else:
             placement.add_device( route.Device( l[0], l[1], l[2], l[3], idx, y, 2))
             print '   placement.add_device( Device( %s, %d, %s, 2))' % (', '.join( map( lambda n: ("'%s'" % n), l)),idx,ty+'y')

  else: # linta   
     for d in sch.devices:
        y = py if d.ty == 'p' else ny
        placement.add_device( route.Device( d.terminals['d'], d.terminals['g'], d.terminals['s'], d.ty, d.x, y, 2))


  s = pysat.Sat( use_picosat=args.use_picosat, use_eureka=args.use_eureka)
  mgr = pysat.VarMgr( s)

  nl = route.Netlist( s, mgr, fn, fabric)

  placement.populate_netlist( nl, args.nets)
  nl.placement = placement

  nl.semantic()

  if args.restrictions:
     counts = {}
     with open( args.restrictions, "r") as fp:
        current_net = None
        p_comment = re.compile( '^#')
        p_nm = re.compile( '^(\S+)\s*$')
        p_pair = re.compile( '^   (\S+)\s+(\S+)[\s+(\S+)]\s*$')
        for line in fp:
           m = p_comment.match( line)         
           if m:
              continue
           m = p_nm.match( line)         
           if m:
              current_net = m.groups()[0]
              counts[current_net] = {}
              continue
           m = p_pair.match( line)         
           if m:
              counts[current_net][m.groups()[0]] = int(m.groups()[1])
              continue
           assert False

     for (k,tbl) in counts.items(): 
        for net in nl.nets:
           if net.p.nm == k:
              for (ly,kount) in tbl.items(): 
                 net.p.limit_segs( ly, kount)
           for tie in net.ties:
              if tie.p.nm == k:
                 for (ly,kount) in tbl.items(): 
                    tie.p.limit_segs( ly, kount)

  for n in ['vss','vcc']:
    for ly in ['via0', 'viacn', 'via0miv', 'via0b', 'viacnb']:
      pass
#      if n in nl.net_hash:
#         nl.net_hash[ n].p.limit_segs( ly, 4)

  for n in ['vcc']:
    for ly in ['diffcon', 'polycon', 'wirepoly']:
      if fabric.isReg():
         if n in nl.net_hash:
            nl.net_hash[ n].p.limit_segs( ly, 0)

  for n in ['vss']:
    for ly in ['diffconb', 'polyconb', 'wirepolyb', 'viacnb']:
      if fabric.isReg():
         if n in nl.net_hash:
            nl.net_hash[ n].p.limit_segs( ly, 0)


  for net in nl.nets:
     for tie in net.ties:
        if args.bounding_box_relaxation >= 0:
           tie.limit_bounding_box( (args.bounding_box_relaxation,None,1))


  nl.route()
  nl.no_shorts()
  nl.no_drvs()

  print 'Writing out constraints'
  s.solve()
  if s.indicator == 'SAT':
    nl.global_p.check_vertical_le_spacing( 'm1', 'metal1')
    nl.global_p.check_vertical_le_spacing( 'm1', 'metal1b')
    nl.global_p.check_vertical_le_spacing( 'dc', 'diffcon')
    nl.global_p.check_vertical_le_spacing( 'dc', 'diffconb')

    nl.global_p.check_connectivity()

    for net in nl.nets:
       net.check_connectivity()

    nl.gen_cleaned_segs()

    nl.gen_stats()

    if not args.no_rpg:
       nl.gen_rpg()
    if not args.no_svg:
       nl.gen_svg()
    with open( '__solution', 'w') as sfp:
       nl.print_solution( sfp)
    if not args.no_tk:
       nl.gen_tk()

  elif s.indicator == 'UNSAT':
    if args.use_picosat or args.use_eureka:
       p_nm = re.compile( '^(.*)_edge_(.*)$')
       def f( v, idx, vv):
          m = p_nm.match( v.nm)
          if m:
             nm = m.groups()[0]
             nm_idx = int(m.groups()[1])
             ( e_idx, ( e, nd0, nd1)) = fabric.indexed_graph_edges[nm_idx]
             assert e_idx == nm_idx
             return ( nm, (e,nd0,nd1))
          else:
             return (v,idx)

       s.report_unsat_core( mgr, f)


import parse_sch

def parse( fn):
  sch = parse_sch.Sch()
  with open(fn, "r") as fp:
     sch.parse( fp)
  print len(sch.devices)
  return (sch,add_from_sch( sch))

def parse_snp( fn):
  sch = parse_sch.Sch()
  with open(fn, "r") as fp:
     sch.parse_snp( fp)
#  print len(sch.devices)
  return (sch,add_from_sch( sch))

def parse_linta( fn):
  sch = parse_sch.Sch()
  with open(fn, "r") as fp:
     sch.parse_linta( fp)
  print len(sch.devices)
  return (sch,add_from_sch( sch))

def assert_lite( pred, errmsg=''):
   if pred:
      pass
   else:
      print 'Assert-Lite', errmsg
  
def display_placement( sbtp, sch, device_placement):
   device_hash = dict( [ (dev.nm, dev) for dev in sch.devices])

   diff_raster = {}
   poly_raster = {}

   bad = False

   for ( dev_nm, ( x, y, f)) in device_placement.items():
      dev = device_hash[dev_nm]

      if f == 'i':
         below_sd = dev.terminals['d']
         above_sd = dev.terminals['s']
      elif f == 'd':
         above_sd = dev.terminals['d']
         below_sd = dev.terminals['s']
      else:
         assert False

#      print 'Placing at', (x,y,f), dev, below_sd, above_sd

      k = ( x, y+1)
      if k in diff_raster:
         if above_sd != diff_raster[k][0]:
            print 'Diff', above_sd, 'at', k, 'already occuppied by', diff_raster[k], ' ', device_placement[diff_raster[k][1].nm]
            bad = True
      else:
#         print 'Assigning diff', k, 'to', above_sd
         diff_raster[k] = ( above_sd, dev)

      k = ( x, y)
      if k in diff_raster:
         if below_sd != diff_raster[k][0]:
            print 'Diff', below_sd, 'at', k, 'already occuppied by', diff_raster[k], ' ', device_placement[diff_raster[k][1].nm]
            bad = True
      else:
#         print 'Assigning diff', k, 'to', below_sd
         diff_raster[k] = ( below_sd, dev)

      assert k not in poly_raster

      poly_raster[k] = dev.terminals['g']

   assert not bad


   for y in range(sbtp.nrows-1,-1,-1):
     for row in ['sd1','ply','sd0']:

        if y > 0 and row == 'sd0': 
#           pass
           continue

        if row in ['sd0','sd1']:
           print 'sd ', ":",
        else:
           print row, ":",

        for x in range( sbtp.ncols):

           diff_bot = diff_raster[ ( x, y)][0] if ( x, y) in diff_raster else '<UNKNOWN>'
           diff_top = diff_raster[ ( x, y+1)][0] if ( x, y+1) in diff_raster else '<UNKNOWN>'

           gate = poly_raster[ ( x, y)] if ( x, y) in poly_raster else '<UNKNOWN>'

           if   row == 'sd1':
              if diff_top == '<UNKNOWN>':
                 print "%8s" % "", 
              else:
                 print "%8s" % diff_top,
           elif row == 'ply':        
              if gate == '<UNKNOWN>':
                 print "%8s" % ' ------ ',
              else:
                 print "%8s" % gate,
           elif row == 'sd0':        
              if diff_bot == '<UNKNOWN>':
                 print "%8s" % "", 
              else:
                 print "%8s" % diff_bot,
           else:
                 assert False

        print


def gen_tiled_placement( sch, Gs, args):
  (GP, GN) = Gs
  sbtp = SatBasedTiledPlacement( args.ncols, args.nrows, args)
  sbtp.build( GP, GN, sch)

  device_hash = dict( [ (dev.nm, dev) for dev in sch.devices])

  for e in GN.edges(keys=True,data=True) + GP.edges(keys=True,data=True):
     n0 = e[0]
     n1 = e[1]
     k  = e[2]      
     g  = e[3]['label']

     assert device_hash[k].terminals['s'] == n0, (n0,device_hash[k])
     assert device_hash[k].terminals['d'] == n1, (n1,device_hash[k])
     assert device_hash[k].terminals['g'] == g, (g,device_hash[k])

  if sbtp.limit_channel_width >= 0:
     for row in range( sbtp.nrows):
        sbtp.emit_poly_channel_constraints( row)
     for row in range( sbtp.nrows+1):
        sbtp.emit_diff_channel_constraints( row)

  sbtp.solve()

  if sbtp.s.indicator == 'UNSAT':
     return

  if sbtp.nsols > 1:

     def intlog10( x):
        ( n, y) = ( 0, 1)
        while y <= x: ( n, y) = ( n+1, y*10)
        return n

     sols = len( sbtp.s.all_models)     
     digits = intlog10( sols - 1 ) if sols > 1 else 1
     fn_pattern = "__snp_%0" + str(digits) + "d"

     for ( idx, mdl) in enumerate( sbtp.s.all_models):
        if idx > 0:
           print 32*'='
        print "Model:", idx

        device_placement = sbtp.extract_device_placement_iv( mdl)

        sch.print_snp( ( fn_pattern % idx), device_placement, args.rotate_snp)

        display_placement( sbtp, sch, device_placement)

     
  else:
     device_placement = {}
     for y in range(sbtp.nrows-1,-1,-1):
        for x in range( sbtp.ncols):
           idx = sbtp.devIdx( x, y)

           unflp = sbtp.unflipped[idx].val()
           flp   = sbtp.flipped[idx].val()

           if unflp != '<UNKNOWN>':
              device_placement[unflp] = ( x, y, 'd')
           if flp != '<UNKNOWN>':
              device_placement[flp]   = ( x, y, 'i')              

     sch.print_snp( "__snp", device_placement, args.rotate_snp)

     display_placement( sbtp, sch, device_placement)



def gen_latch_fabric( sch, Gs, args):
  (GP, GN) = Gs

  lf = LatchFabric10nm( GP, GN, args.limit_channel_width, args.extra_units, args.blank_half_cell)
  lf.solve()
  lf.report()

  with open( ('%s.py' % sch.cellname), 'w') as fp:
     fp.write( u'#!/usr/bin/env python\n')
     fp.write( u'\n')
     fp.write( u'import sys\n')
     fp.write( u'sys.path.append( "../..")\n')
     fp.write( u'import ag\n')
     fp.write( u'import fg\n')
     fp.write( u'\n')
     fp.write( u'def gen_fabric_%s( a):\n' % sch.cellname)
     fp.write( u'  c = fg.Cell( a, \'%s\')\n' % sch.cellname)     
     fp.write( u'\n')
     fp.write( u'  c.il = [ %s]\n' % (', '.join( map( lambda i: (u'\'%s\'' % i), sch.inputs))))
     fp.write( u'  c.ol = [ %s]\n' % (', '.join( map( lambda i: (u'\'%s\'' % i), sch.outputs))))
     fp.write( u'\n')
     lf.fancy_report( fp)
     fp.write( u'\n')
     fp.write( u'  c.write()\n')
     fp.write( u'\n')
     fp.write( u'if __name__ == "__main__":\n')
     fp.write( u'  a = ag.gen_arch_latch_15dg_kolya()\n')
     fp.write( u'  with open( "xxx.laygen", "w") as fp:\n')
     fp.write( u'    a.write( fp)\n')
     fp.write( u'  gen_fabric_%s( a)\n' % sch.cellname)

  with open( ('%s-route.csh' % sch.cellname), 'w') as fp:
     fp.write( u'#!/bin/csh -f\n')
     fp.write( u'\n')

#     non_rail_nets = list( sets.Set(sch.nets()) - sets.Set(['vcc','vss']))
     all_nets = list( sets.Set(sch.nets()))

     fp.write( u'$CELLGEN/bin/sgrlfg -fabric xxx -architecture_file xxx.laygen -netlist %s.snp -complexity 4 -upperlayer m2 -nets %s\n' % (sch.cellname, ','.join( all_nets)))


class Range:
  def __init__( self, x):
     ( self.lb, self.ub) = (x,x)

  def update( self, x):
     self.lb = min(self.lb,x)
     self.ub = max(self.ub,x)

class Anet:
  def __init__( self, x, y):
     self.xrange = Range( x)
     self.yrange = Range( y)

  def update( self, x, y):
     self.xrange.update( x)
     self.yrange.update( y)

def analyze( sch, fn):

  nets = {}
  def add_net( n, x, y):
     if n not in nets:
        nets[n] = Anet( x, y)
     else:
        nets[n].update( x, y)

  minx =  1000000
  maxx = -1000000

  for d in sch.devices:

     assert d.ty == 'p' or d.ty == 'n'

     r = d.placement[0]
     x = d.placement[1]
     y = d.placement[2]
     flip = d.placement[3] == 'i'

     if x < minx: minx = x
     if x > maxx: maxx = x

#
# Specific to SAGE
#
#     assert y == 0

     if d.ty == 'p':
        if r == 1:
           true_y = 2
        else:
           true_y = 1
     else:
        if r == 1:
           true_y = 3
        else:
           true_y = 0

     (sd0,sd1) = (d.terminals['d'],d.terminals['s']) if not flip else (d.terminals['s'],d.terminals['d'])

     g = d.terminals['g']

     add_net( sd0, d.placement[1]*2+1, true_y)
     add_net( g,   d.placement[1]*2+2, true_y)
     add_net( sd1, d.placement[1]*2+3, true_y)

  all_xs = [ x for (k,v) in nets.items() for x in [v.xrange.lb,v.xrange.ub] ]
  all_ys = [ x for (k,v) in nets.items() for x in [v.yrange.lb,v.yrange.ub] ]

  max_channel_capacity = 0
  for x in range(max(all_xs)+1):
     count = 0
     for (k,v) in nets.items():
        if k in ['vss','vcc']: continue
        xlb = v.xrange.lb
        xub = v.xrange.ub
        if xub - xlb < 2:
           if xlb-1 <= x and x <= xub+1: count += 1
        else:
           if xlb <= x and x <= xub: count += 1

     max_channel_capacity = max(count,max_channel_capacity)
  
  semi_perimeter = 0
  for (k,v) in nets.items():
     if k in ['vss','vcc']: continue
     semi_perimeter += v.xrange.ub-v.xrange.lb + 3*( v.yrange.ub-v.yrange.lb)

  l_boundary_output = False
  r_boundary_output = False
  for d in sch.devices:

     assert d.ty == 'p' or d.ty == 'n'

     x = d.placement[1]
     flip = d.placement[3] == 'i'

     (sd0,sd1) = (d.terminals['d'],d.terminals['s']) if not flip else (d.terminals['s'],d.terminals['d'])

     if x == 0 and sd0 in sch.outputs:
        l_boundary_output = True

     if x == maxx and sd1 in sch.outputs:
        r_boundary_output = True

  print fn, "Capacity:", max_channel_capacity, "Wirelength:", semi_perimeter, "Width:", maxx-minx+1, minx, maxx, "Bound_Output:", l_boundary_output, r_boundary_output

if __name__ == "__main__":

  import sys
  import argparse

  parser = argparse.ArgumentParser( description="Place devices in fabric.")

  parser.add_argument( '-limit_channel_width', type=int, default=-1)
  parser.add_argument( '-extra_units', type=int, default=0)
  parser.add_argument( '-blank_half_cell', action='store_true')

  parser.add_argument( '-tiled_placer', action='store_true')
  parser.add_argument( '-fabric', action='store_true')

  parser.add_argument( '-threed', type=str, default="Fabric3D")
  parser.add_argument( '-partition', action='store_true')
  parser.add_argument( '-analyze', action='store_true')
  parser.add_argument( '-limit_crossings', type=int, default=0)
  parser.add_argument( '-all_sat', action='store_true')

  parser.add_argument( '-extra_cols', type=int, default=0)
  parser.add_argument( '-ncols', type=int, default=0)
  parser.add_argument( '-nrows', type=int, default=0)
  parser.add_argument( '-rotate_snp', action='store_true')
  parser.add_argument( '-nsols', type=int, default=1)

  parser.add_argument( '-limit_different_polys', type=int, default=0)
  parser.add_argument( '-nets', type=str, default=None)

  parser.add_argument( '-no_svg', action='store_true')
  parser.add_argument( '-no_rpg', action='store_true')
  parser.add_argument( '-no_tk', action='store_true')

  parser.add_argument( '-restrictions', type=str, default=None)
  parser.add_argument( '-bounding_box_relaxation', type=int, default=1)

  parser.add_argument( '-linta', action='store_true')
  parser.add_argument( '-snp', action='store_true')
  parser.add_argument( '-use_picosat', action='store_true')
  parser.add_argument( '-use_eureka', action='store_true')

  parser.add_argument( '-exclude_poly_triples', action='store_true')
  parser.add_argument( '-exclude_tcn_triples', action='store_true')

  parser.add_argument( 'fn', metavar='<sch file name>')

  args = parser.parse_args()

  
  if args.linta:
     (sch, (GP, GN)) = parse_linta( args.fn)
     (root, ext) = os.path.splitext( os.path.basename( args.fn))
     sch.cellname = root
  elif args.snp:
     (sch, (GP, GN)) = parse_snp( args.fn)
  else:
     (sch, (GP, GN)) = parse( args.fn)

  if args.analyze:
     analyze( sch, args.fn)

  elif args.fabric:
     gen_latch_fabric( sch, (GP, GN), args)

  elif args.tiled_placer:
     gen_tiled_placement( sch, (GP, GN), args)

  elif args.partition:
     part = SatPartition( GP, GN, args)

     if args.all_sat:
        pass

     elif part.s.indicator == 'SAT':

        (GP0,GP1) = part.p_row.split()
        (GN0,GN1) = part.n_row.split()

        print '|P0|:', len(GP0.edges(keys=True,data=True))
        print '|N0|:', len(GN0.edges(keys=True,data=True))
        print '|P1|:', len(GP1.edges(keys=True,data=True))
        print '|N1|:', len(GN1.edges(keys=True,data=True))

        master = [ e[2] for e in GP0.edges(keys=True,data=True) + GN0.edges(keys=True,data=True)]
        slave  = [ e[2] for e in GP1.edges(keys=True,data=True) + GN1.edges(keys=True,data=True)]

        print "Option name=placement_group_dependency master=%s slave=%s" % ( ','.join( master), ','.join( slave))

#        gen_threed_routing_problem( sch.cellname+'_a', GP0, GN0, args, sch)
#        gen_threed_routing_problem( sch.cellname+'_b', GP1, GN1, args, sch)

  elif not args.partition and args.threed:
     gen_threed_routing_problem( sch.cellname, GP, GN, args, sch)

  else:
     print 'Neither -threed nor -fabric nor -tile_placer specified'
