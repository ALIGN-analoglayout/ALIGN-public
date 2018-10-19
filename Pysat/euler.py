#!/usr/bin/env python

import pytest
import networkx as nx
import tally

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
   
      self.node_values = list(G.nodes())
      print( "node_values:", self.node_values)


      edge_values = [ e[2] for e in G.edges(keys=True)]

      print( "edge_values:", edge_values)


      self.unflipped = [ self.p.mgr.add_var( tally.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('==>[%s]'%idx), edge_values)) for idx in range(0,m) ]
      self.flipped   = [ self.p.mgr.add_var( tally.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('<==[%s]'%idx), edge_values)) for idx in range(0,m) ]

      self.diffs     = [ self.p.mgr.add_var( tally.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('dif[%s]'%idx), self.node_values)) for idx in range(0,m+1) ]

      self.polys = [ self.p.mgr.add_var( tally.PossiblyUnknownEnumVar( self.p.s, self.row_nm+('ply[%s]'%idx), self.p.gate_values)) for idx in range(0,m) ]



#
# For each transistor, make sure that it is instantiated at least once
#
      for ev in edge_values:
         self.p.s.emit_exactly_one( [ t.var(ev) for t in self.unflipped + self.flipped])

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
         self.p.s.emit_and( [c1, tally.Tally.neg( self.same_diffs[idx])], q0)
         q1 = self.p.s.add_var()
         self.p.s.emit_or( [q0,self.different_diffs[idx]], q1)
         self.p.s.emit_and( [tally.Tally.neg( self.tran_defined[idx]), q1], self.different_diffs_and_unknown_tran[idx])
            

#      self.count_different_diffs_and_unknown_tran = [ self.p.s.add_var() for idx in range(0,m) ]
#      self.p.s.emit_tally( self.different_diffs_and_unknown_tran, self.count_different_diffs_and_unknown_tran)



class SatBasedEulerPaths:
   def __init__( self):
      self.s   = tally.Tally()
      self.mgr = tally.VarMgr( self.s)
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
         [ e[3]['label'] for e in GP.edges(keys=True,data=True)] + \
         [ e[3]['label'] for e in GN.edges(keys=True,data=True)]))

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
         for (nval,nvar) in zip( n.vals, n.vars):
            if nval in p_dict:
               same_diff.append( self.s.add_var())
               self.s.emit_and( [p_dict[nval],nvar], same_diff[-1])

         self.same_p_and_n_diffusions.append( self.s.add_var())
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

      left_scan = [ self.mgr.add_var( tally.PowerSetEnumVar( self.s, 'ls[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]

      left_scan_in = []
      for idx in range(0,m):
         left_scan_in.append( [ self.row_p.diffs[idx], self.row_n.diffs[idx]])
         if idx < m-1:
            left_scan_in.append( [ self.row_p.polys[idx], self.row_n.polys[idx]])

      assert all( [ len(l) <= 2 for l in left_scan_in])

      self.build_scan( m, left_scan, left_scan_in)

      right_scan = [ self.mgr.add_var( tally.PowerSetEnumVar( self.s, 'rs[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]
      right_scan.reverse()

      right_scan_in = [ l[:] for l in left_scan_in[:] ] # explicit deep copy
      right_scan_in.reverse()

      self.build_scan( m, right_scan, right_scan_in)

      right_scan.reverse()

      and_of_scans = [ self.mgr.add_var( tally.PowerSetEnumVar( self.s, 'as[%02d]'%idx, self.all_net_values)) for idx in range(len(self.row_p.polys + self.row_p.diffs)) ]

      for ((l,r),q) in zip( zip( left_scan, right_scan), and_of_scans):      
         for val in q.vals:
            self.s.emit_and( [ l.var( val), r.var( val)], q.var( val))

      for q in and_of_scans:
         outs = [ self.s.add_var() for idx in range(self.limit_channel_width+1)]
         self.s.emit_tally( [ vr for (vl,vr) in zip(q.vals,q.vars) if vl not in ['vss','vcc']], outs)
         self.s.emit_never( outs[-1])

   def solve( self):
      self.s.solve()
      if self.s.state == 'UNSAT':
         print( 'UNSAT')
      else:     
         assert self.s.state == 'SAT'
         print( 'SAT')

         for nm,v in sorted( self.mgr.nm_map.items()):
            pass
            print( '%s=%s'%(nm, v.val()))

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

class SatPartitionAux:
   def __init__( self, dad, ty, G):
      self.dad = dad
      self.ty = ty
      self.G = G
      self.edges = G.edges( keys=True, data=True)
      self.vars = [ self.dad.mgr.add_var( tally.BitVar( self.dad.s, ('%s_edge_%d' % (ty,idx)))) for (idx,e) in enumerate(self.edges)]
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

#      print( nets)

      n = len(self.edges)
      out_vars = [ self.dad.s.add_var() for idx in range(n+1)]

      self.dad.s.emit_tally( [ v.var() for v in self.vars], out_vars)
      
      if n % 4 == 2:
         assert n >= 2
         limit = n//2 + 1 
         print( "Limiting number of devices in %s master to %d of %d" % (self.ty, limit, n))
         self.dad.s.emit_always( out_vars[limit-1])
         self.dad.s.emit_never( out_vars[limit])
      else:
         assert n >= 2
         limit = n//2
         print( "Limiting number of devices in %s master to %d of %d" % (self.ty, limit, n))
         self.dad.s.emit_always( out_vars[limit-1])
         self.dad.s.emit_never( out_vars[limit])

   def split( self):
      G0 = nx.MultiDiGraph()
      G1 = nx.MultiDiGraph()

      m = dict( [ (v,v.val()) for v in self.vars])

      for ( tuple, var) in zip( self.edges, self.vars):
         ( e0, e1, k, lbl) = tuple
         if m[var]:
            G1.add_edge( e0, e1, key=k, label=lbl['label'])         
         else:   
            G0.add_edge( e0, e1, key=k, label=lbl['label'])         

      return (G0,G1)



class SatPartition:
   def __init__( self, GP, GN, limit_crossings=3):
      """
Divide (GP,GN) into two graphs each, without about half the device (edges) in each graph, minimizing the number of wires that cross 
"""
      self.s   = tally.Tally()
      self.mgr = tally.VarMgr( self.s)
      self.limit_crossings = limit_crossings
      self.all_sat = False

      self.nets = {}
      self.p_row = SatPartitionAux( self, 'p', GP)
      self.n_row = SatPartitionAux( self, 'n', GN)

      self.semantic()


   def print_model( self):

      if self.s.state == 'SAT':
         
         in_common = {}
         only_in_off = {}
         only_in_on = {}

         for ( (k, v), net_var) in zip( self.lst, self.net_vars):
            if k in ['vss','vcc']:
               in_common[k] = True
               print( 'rail', net_var)
            elif net_var.val():
               in_common[k] = True
               print( 'crossing', net_var)
            else:
               print( 'no crossing', net_var)
               for ( ty, idx) in v:
                  assert ty in ['p','n']
                  if   ty == 'p':
                     vv = self.p_row.vars[idx].val()
                  elif ty == 'n':
                     vv = self.n_row.vars[idx].val()
                  if vv:
                     only_in_on[k] = True   
                  else:
                     only_in_off[k] = True   

            for ( ty, idx) in v:
               assert ty in ['p','n']
               if   ty == 'p':
                  vv = self.p_row.vars[idx].val()
               elif ty == 'n':
                  vv = self.n_row.vars[idx].val()
               print( '   ', ty, idx, vv)


         print( 'Nets in common:', in_common.keys())
         print( 'Nets in master:', only_in_on.keys())
         print( 'Nets in slave:', only_in_off.keys())

         for nm,v in sorted( self.mgr.nm_map.items()):
            pass
#            print( '%s=%s'%(nm, v.val()))


   def semantic( self):
      self.lst = [ (k, set( v)) for ( k, v) in self.nets.items()]

      self.net_vars = [ self.mgr.add_var( tally.BitVar( self.s, ('net_%s' % k))) for (k, v) in self.lst]

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
            assert ty in ['p','n']
            if   ty == 'p':
               vv = self.p_row.vars[idx].var()
            elif ty == 'n':
               vv = self.n_row.vars[idx].var()
            or_on_vars.append( vv)             
            or_off_vars.append( tally.Tally.neg( vv))

         self.s.emit_or( or_on_vars, one_on)
         self.s.emit_or( or_off_vars, one_off)

      out_vars = [ self.s.add_var() for idx in range( self.limit_crossings+1)]

      self.s.emit_tally( [ v.var() for v in self.net_vars], out_vars)
      self.s.emit_never( out_vars[-1])

      self.s.solve()
      self.print_model()

def test_euler_aoi022():
  print( "aoi022")

  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

  GP.add_edge( "vcc", "n1", key="pa", label="a")
  GP.add_edge( "vcc", "n1", key="pb", label="b")
  GP.add_edge( "n1",  "o1", key="pc", label="c")
  GP.add_edge( "n1",  "o1", key="pd", label="d")

  GN.add_edge( "vss", "n2", key="na", label="a")
  GN.add_edge( "n2",  "o1", key="nb", label="b")
  GN.add_edge( "vss", "n3", key="nc", label="c")
  GN.add_edge( "n3",  "o1", key="nd", label="d")

  print( GP.edges(keys=True,data=True))
  print( GN.edges(keys=True,data=True))

  sbep = SatBasedEulerPaths()
  sbep.limit_channel_width = 3
  sbep.sat_based_euler_paths( GP, GN)
  sbep.solve()
  assert sbep.s.state == 'SAT'

def test_euler_nand02_one():
  print( "nand02")

  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

  GP.add_edge( "vcc", "o1", key="pa", label="a")
  GP.add_edge( "vcc", "o1", key="pb", label="b")

  GN.add_edge( "vss", "n1", key="na", label="a")
  GN.add_edge( "n1",  "o1", key="nb", label="b")

  print( GP.edges(keys=True,data=True))
  print( GN.edges(keys=True,data=True))

  sbep = SatBasedEulerPaths() 
  sbep.limit_channel_width = 1
  sbep.sat_based_euler_paths( GP, GN)
  sbep.solve()
  assert sbep.s.state == 'UNSAT'

@pytest.mark.skip(reason="Takes too long.")
def test_euler_ru0023( extra_cols=2, max_capacity=6):
  print( "ru0023 %d %d" % (extra_cols, max_capacity))

  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

  GP.add_edge( "vcc", "n9",  key="M02", label="n10")
  GP.add_edge( "vcc", "n10", key="M01", label="a")
  GN.add_edge( "vss", "n9",  key="M16", label="n10")
  GN.add_edge( "vss", "n10", key="M15", label="a")

  GP.add_edge( "n9",  "carry",  key="M13", label="n16")
  GP.add_edge( "n10", "sum",    key="M11", label="n16")
  GN.add_edge( "n9",  "carry",  key="M27", label="n11")
  GN.add_edge( "n10", "sum",    key="M25", label="n11")
  GP.add_edge( "n15", "carry",  key="M14", label="n11")
  GP.add_edge( "n9",  "sum",    key="M12", label="n11")
  GN.add_edge( "n15", "carry",  key="M28", label="n16")
  GN.add_edge( "n9",  "sum",    key="M26", label="n16")

  GP.add_edge( "vcc", "n15",    key="M06", label="n13")
  GN.add_edge( "vss", "n15",    key="M20", label="n13")
  GP.add_edge( "vcc", "n12",    key="M03", label="b")
  GP.add_edge( "n12", "n11",    key="M10", label="n13")
  GN.add_edge( "vss", "n12",    key="M17", label="b")
  GN.add_edge( "n12", "n16",    key="M21", label="n13")

  GP.add_edge( "n12", "n16",    key="M07", label="n15")
  GP.add_edge( "n14", "n11",    key="M09", label="n15")
  GN.add_edge( "n12", "n11",    key="M24", label="n15")
  GN.add_edge( "n14", "n16",    key="M22", label="n15")
  GP.add_edge( "n14", "n16",    key="M08", label="n13")
  GP.add_edge( "vcc", "n14",    key="M04", label="n12")
  GN.add_edge( "n14", "n11",    key="M23", label="n13")
  GN.add_edge( "vss", "n14",    key="M18", label="n12")
  GP.add_edge( "vcc", "n13",    key="M05", label="c")
  GN.add_edge( "vss", "n13",    key="M19", label="c")


  print( GP.edges(keys=True,data=True))
  print( GN.edges(keys=True,data=True))

  sbep = SatBasedEulerPaths()
  sbep.extra_cols = extra_cols
  sbep.limit_channel_width = max_capacity
  sbep.sat_based_euler_paths( GP, GN)
  sbep.solve()
  assert sbep.s.state == 'SAT'


def test_sat_partition_nand03_doubled():
  print( "nand03")

  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

  GP.add_edge( "vcc", "o1", key="p0a", label="a")
  GP.add_edge( "vcc", "o1", key="p0b", label="b")
  GP.add_edge( "vcc", "o1", key="p0c", label="c")
  GP.add_edge( "vcc", "o1", key="p1a", label="a")
  GP.add_edge( "vcc", "o1", key="p1b", label="b")
  GP.add_edge( "vcc", "o1", key="p1c", label="c")

  GN.add_edge( "vss", "n1", key="n0a", label="a")
  GN.add_edge( "n1",  "n2", key="n0b", label="b")
  GN.add_edge( "n2",  "o1", key="n0c", label="c")
  GN.add_edge( "vss", "n1", key="n1a", label="a")
  GN.add_edge( "n1",  "n2", key="n1b", label="b")
  GN.add_edge( "n2",  "o1", key="n1c", label="c")

  print( GP.edges(keys=True,data=True))
  print( GN.edges(keys=True,data=True))

  sp = SatPartition( GP, GN, 2)
  assert sp.s.state == 'SAT'

  (GP0,GP1) = sp.p_row.split()
  (GN0,GN1) = sp.n_row.split()
  print( GP0.edges(keys=True,data=True))
  print( GP1.edges(keys=True,data=True))
  print( GN0.edges(keys=True,data=True))
  print( GN1.edges(keys=True,data=True))


def test_sat_partition_aoi022():

  GP = nx.MultiDiGraph()
  GN = nx.MultiDiGraph()

#  GP.add_nodes_from( ["vcc","n1","o1"])
  GP.add_edge( "vcc", "n1", key="pa", label="a")
  GP.add_edge( "vcc", "n1", key="pb", label="b")
  GP.add_edge( "n1",  "o1", key="pc", label="c")
  GP.add_edge( "n1",  "o1", key="pd", label="d")

#  GN.add_nodes_from( ["vss","n2","n3","o1"])
  GN.add_edge( "vss", "n2", key="na", label="a")
  GN.add_edge( "n2",  "o1", key="nb", label="b")
  GN.add_edge( "vss", "n3", key="nc", label="c")
  GN.add_edge( "n3",  "o1", key="nd", label="d")

  print( GP.edges(keys=True,data=True))
  print( GN.edges(keys=True,data=True))

  sp = SatPartition( GP, GN, 2)
  assert sp.s.state == 'SAT'

  (GP0,GP1) = sp.p_row.split()
  (GN0,GN1) = sp.n_row.split()
  print( GP0.edges(keys=True,data=True))
  print( GP1.edges(keys=True,data=True))
  print( GN0.edges(keys=True,data=True))
  print( GN1.edges(keys=True,data=True))

if __name__ == "__main__":
  test_euler_ru0023(2,6)
