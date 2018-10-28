#!/usr/bin/env python

import tally
import json
from collections import OrderedDict
import itertools

"""
Placer problem:
There is an ADT grid.
+-------++-------++-------++-------++-------++-------++-------++-------+
|  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  |
+---v---++---v---++---v---++---v---++---v---++---v---++---v---++---v---+
+---^---++---^---++---^---++---^---++---^---++---^---++---^---++---^---+
|  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  |
+-------++-------++-------++-------++-------++-------++-------++-------+
+-------++-------++-------++-------++-------++-------++-------++-------+
|  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  |
+---v---++---v---++---v---++---v---++---v---++---v---++---v---++---v---+
+---^---++---^---++---^---++---^---++---^---++---^---++---^---++---^---+
|  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  |
+-------++-------++-------++-------++-------++-------++-------++-------+
+-------++-------++-------++-------++-------++-------++-------++-------+
|  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  |
+---v---++---v---++---v---++---v---++---v---++---v---++---v---++---v---+
+---^---++---^---++---^---++---^---++---^---++---^---++---^---++---^---+
|  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  |
+-------++-------++-------++-------++-------++-------++-------++-------+
+-------++-------++-------++-------++-------++-------++-------++-------+
|  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  ||  <P>  |
+---v---++---v---++---v---++---v---++---v---++---v---++---v---++---v---+
+---^---++---^---++---^---++---^---++---^---++---^---++---^---++---^---+
|  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  ||  <N>  |
+-------++-------++-------++-------++-------++-------++-------++-------+
Each ADT exposes nets on their left and right, so the placer must prevent shorts.
This can be modeled as a shared m1 track on the left and right boundaries of the ADT.
The placer will determine whether to flip around the y-axis, to make the necessary connections.

The cells will also need to be flipped around the x-axis depending on position in the grid.
Let's number these using the lower left corner as (0,0).
Rows where y % 4 == 0 are unflipped N ADTs.
Rows where y % 4 == 1 are   flipped P ADTs.
Rows where y % 4 == 2 are unflipped P ADTs.
Rows where y % 4 == 3 are   flipped N ADTs.


We want to be able to place larger than one ADT entities.
So we have things like this:
+---^---+
|t0<N>t1|
+-------+
or like this:
+---^---++---^---+
|t0<N>t1||t1<N>t2|
+-------++-------+
or like this:
+---^---++---^---+
|t0<P>t1||t1<P>t2|
+-------++-------+
+-------++-------+
|t2<P>t3||t3<P>t4|
+---v---++---v---+
but not anything that looks like this (can't fit anywhere in the grid):
+-------++-------+
|t0<P>t1||t1<P>t2|
+---v---++---v---+
+---^---++---^---+
|t2<P>t3||t3<P>t4|
+-------++-------+
or like this (3 adjacent N rows not in grid):
+-------++-------+
|t0<N>t1||t1<N>t2|
+---v---++---v---+
+---^---++---^---+
|t2<N>t3||t3<N>t4|
+-------++-------+
+-------++-------+
|t5<N>t6||t6<P>t7|
+---v---++---v---+
"""

class Tech:
# Mock the tech file to temporarily simplify integration
  def __init__( self):
      self.halfXADTGrid = 1
      self.halfYADTGrid = 1
      self.pitchPoly   = 720
      self.pitchDG     = 720
      self.verticalMetals = ["metal1","metal3","metal5"]
      self.horizontalMetals = ["metal2","metal4"]

class Rect:
  def __init__( self, llx=None, lly=None, urx=None, ury=None):
      self.llx = llx
      self.lly = lly
      self.urx = urx
      self.ury = ury

  def canonical( self):
      [llx,lly,urx,ury] = self.toList()
      if llx > urx: llx,urx = urx,llx
      if lly > ury: lly,ury = ury,lly
      return Rect( llx,lly,urx,ury)

  def toList( self):
      return [self.llx, self.lly, self.urx, self.ury]

  def __repr__( self):
    return str(self.toList())

class Transformation:
    def __init__( self, oX=0, oY=0, sX=1, sY=1):
        self.oX = oX
        self.oY = oY
        self.sX = sX
        self.sY = sY

    def hit( self, p):
        x,y = p
        return self.sX * x + self.oX, self.sY * y + self.oY

    def hitRect( self, r):
        llx,lly = self.hit( (r.llx, r.lly))
        urx,ury = self.hit( (r.urx, r.ury))
        return Rect( llx, lly, urx, ury)

    @staticmethod
    def mult( A, B):
        # A.sX 0    A.oX     B.sX 0    B.oX
        # 0    A.sY A.oY     0    B.sY B.oY
        # 0    0    1        0    0    1
        C = Transformation()
        C.sX = A.sX * B.sX
        C.sY = A.sY * B.sY
        C.oX = A.sX * B.oX + A.oX
        C.oY = A.sY * B.oY + A.oY
        return C

    def preMult( self, A):
      return self.__class__.mult( A, self)

    def postMult( self, A):
      return self.__class__.mult( self, A)

def test_transformation_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_transformation_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

def test_transformation_Mult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (Transformation.mult( b, a)).hit( (0,0))

def test_transformation_preMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (a.preMult(b)).hit( (0,0))

def test_transformation_postMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (b.postMult(a)).hit( (0,0))

class Terminal:
  def __init__( self, nm, layer, r):
    self.nm = nm
    self.layer = layer
    self.r = r

def encode_T( tech, obj):
  if isinstance(obj, Rect):
    r = Rect()
    r.llx = tech.pitchPoly*tech.halfXADTGrid*2*obj.llx
    r.urx = tech.pitchPoly*tech.halfXADTGrid*2*obj.urx
    r.lly = tech.pitchDG  *tech.halfYADTGrid*2*obj.lly
    r.ury = tech.pitchDG  *tech.halfYADTGrid*2*obj.ury 
    return r.toList()
  elif isinstance(obj, Terminal):
    if obj.layer == 'metal1':
      r = Rect()
      r.llx = tech.pitchPoly*tech.halfXADTGrid*2*obj.r.llx - 200
      r.urx = tech.pitchPoly*tech.halfXADTGrid*2*obj.r.urx + 200
      r.lly = tech.pitchDG  *tech.halfYADTGrid*2*obj.r.lly + 360
      r.ury = tech.pitchDG  *tech.halfYADTGrid*2*obj.r.ury - 360
      return { "netName" : obj.nm, "layer" : obj.layer, "rect" : r.toList()}
    else:
      raise TypeError(repr(obj) + (" is not JSON serializable. Unknown terminal layer %s" % obj.layer))
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

class CellTemplate:
    def __init__( self, nm):
        self.nm = nm
        self.terminals = OrderedDict()
        
    def dumpJson( self, fp, tech):
      collect_templates = {}
      for ci in self.instances.values():
        if ci.template.nm not in collect_templates: collect_templates[ci.template.nm] = []
        collect_templates[ci.template.nm].append( ci.template)

      leaves = []
      for (k,v) in collect_templates.items():
        assert len(v) > 0
        terminals = []
        for (net_nm,term_lst) in v[0].terminals.items():
          for term in term_lst:
            terminals.append( { "net_name": net_nm,
                                "layer": "metal1",
                                "rect": term.toList()})
        leaves.append( { "template_name": k,
                         "bbox": v[0].bbox.toList(),
                         "terminals": terminals})

      instances = []
      for (k,ci) in self.instances.items():
        instances.append( { "instance_name": k,
                            "template_name": ci.template.nm,
                            "transformation": { "oX" : ci.transformation.oX,
                                                "oY" : ci.transformation.oY,
                                                "sX" : ci.transformation.sX,
                                                "sY" : ci.transformation.sY},
                            "formal_actual_map": ci.fa_map})

      terminals = []
      for (net_nm,term_lst) in self.terminals.items():
        for term in term_lst:
          terminals.append( { "net_name": net_nm,
                              "layer": "metal1",
                              "rect": term.toList()})

      for (k,ci) in self.instances.items():
        for (net_nm,term_lst) in ci.template.terminals.items():
          for term in term_lst:
            r = ci.transformation.hitRect( term).canonical()
            terminals.append( { "hier_name": k + '/' + net_nm,
                                "net_name": ci.fa_map[net_nm],
                                "layer": "metal1",
                                "rect": r.toList()})

      bbox = self.bbox.toList()
#      bbox[2] += 1
      data = { "nm": self.nm,
               "bbox": bbox,
               "leaves": leaves,
               "instances": instances,
               "terminals": terminals}

      fp.write( json.dumps( data, indent=2) + "\n")


    def addInstance( self, ci):
        self.instances[ci.nm] = ci

    def addTerminal( self, nm, r):
        if nm not in self.terminals: self.terminals[nm] = []
        assert r.llx == r.urx
        assert r.lly < r.ury
        self.terminals[nm].append( r)

    def connect( self, i, p, n):
      self.instances[i].fa_map[p] = n

    def __repr__( self):
        return "CellTemplate(" + nm + "," + self.instances + "," + self.bbox + ")"

    def write_globalrouting_json( self, fp, tech):
        grs = []
        terminals = []

        terminals.append( { "netName" : self.nm, "layer" : "diearea", "rect" : self.bbox})
        for inst in self.instances.values():
            r = inst.transformation.hitRect( inst.template.bbox)
            nm = self.nm + '/' + inst.nm + ':' + inst.template.nm
            terminals.append( { "netName" : nm, "layer" : "cellarea", "rect" : r.canonical()})

        for inst in self.instances.values():
            r = inst.transformation.hitRect( inst.template.bbox)
            for (k,v) in inst.template.terminals.items():
              for term in v:
                nm = self.nm + '/' + inst.nm + '/' + k + ':' + inst.fa_map[k]
                terminals.append( Terminal( nm, "metal1", inst.transformation.hitRect( term).canonical()))

        grGrid = []
        for x in range( self.bbox.llx, self.bbox.urx):
            for y in range( self.bbox.lly, self.bbox.ury):
                grGrid.append( Rect( x,y,x+1,y+1))

        data = { "bbox" : self.bbox, "globalRoutes" : grs, "globalRouteGrid" : grGrid, "terminals" : terminals}

        fp.write( json.dumps( data, indent=2, default=lambda x: encode_T(tech,x)) + "\n")


class CellLeaf(CellTemplate):
    def __init__( self, nm, bbox=None):
        super().__init__(nm)
        if bbox is None:
          self.bbox = Rect(0,0,1,1)
        else:
          self.bbox = bbox

    @property
    def instances( self):
        return OrderedDict()

class CellHier(CellTemplate):
    def __init__( self, nm):
        super().__init__(nm)
        self.instances = OrderedDict()
        self.bbox = None

    def updateBbox( self):
        self.bbox = Rect(None,None,None,None)
        for inst in self.instances.values():
            r = inst.transformation.hitRect( inst.template.bbox).canonical()
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

class CellInstance:
    def __init__( self, nm, template, trans=None):
        self.nm = nm
        self.template = template
        self.transformation = trans
        self.fa_map = OrderedDict()

class RasterInstance:
    def __init__( self, r, ci):
        self.r = r
        self.ci = ci
        self.filled    = tally.BitVec( r.s, ci.nm + '_filled', r.nx*r.ny)
        self.anchor    = tally.BitVec( r.s, ci.nm + '_anchor',   r.nx*r.ny)
        self.anchorMY  = tally.BitVec( r.s, ci.nm + '_anchorMY', r.nx*r.ny)
        self.anchorMX  = tally.BitVec( r.s, ci.nm + '_anchorMX', r.nx*r.ny)
        self.anchorMXY = tally.BitVec( r.s, ci.nm + '_anchorMXY', r.nx*r.ny)
        self.semantic()

    def tGen( self, plusOneIfMirrored=False):
        for x in range(self.r.nx):
            for y in range(self.r.ny):
              o = 1 if plusOneIfMirrored else 0
              pairs = [( self.anchor,    Transformation( x,   y,    1,  1)),
                       ( self.anchorMY,  Transformation( x+o, y,   -1,  1)),
                       ( self.anchorMX,  Transformation( x,   y+o,  1, -1)),
                       ( self.anchorMXY, Transformation( x+o, y+o, -1, -1))]
              for ( bv, tr) in pairs:
                yield ( x, y, bv, tr)

    def backannotatePlacement( self):
      self.ci.transformation = None
      for ( x, y, bv, tr) in self.tGen( plusOneIfMirrored=True):
        if bv.val( self.r.idx( x, y)) is True:
          self.ci.transformation = tr

    def semantic( self):
      print( "Building RasterInstance", self.ci.nm)
      for ( x, y, bv, tr) in self.tGen():      
        anchor = bv.var( self.r.idx( x, y))
        bbox = self.ci.template.bbox
        for xx in range( bbox.llx, bbox.urx):
          for yy in range( bbox.lly, bbox.ury):
            (xxx,yyy) = tr.hit( (xx,yy))
            if 0 <= xxx and xxx < self.r.nx and 0 <= yyy and yyy < self.r.ny:
              self.r.s.emit_implies( anchor, self.filled.var( self.r.idx( xxx, yyy)))
            else:
              self.r.s.emit_never( anchor)

      allCand    = [self.anchor.var( i)    for i in range( self.r.nx*self.r.ny)]
      allCandMY  = [self.anchorMY.var( i)  for i in range( self.r.nx*self.r.ny)]
      allCandMX  = [self.anchorMX.var( i)  for i in range( self.r.nx*self.r.ny)]
      allCandMXY = [self.anchorMXY.var( i) for i in range( self.r.nx*self.r.ny)]

      self.r.s.emit_exactly_one( allCand + allCandMY + allCandMX + allCandMXY)


class Raster:
    def __init__( self, s, template, nx, ny):
        self.s = s    
        self.template = template
        self.ris = []
        self.nx = nx
        self.ny = ny

    def idx( self, x, y):
        return x*self.ny + y

    def addTerminalOverlapConstraints( self):
        print( "Building bit vectors for %d nets" % len(self.nets))

        self.net_bvs = OrderedDict()
        for k in self.nets.keys():
          self.net_bvs[k] = tally.BitVec( self.s, ('net_terminal_%s' % k), (self.nx+1)*self.ny)

        for ri in self.ris:
          inst = ri.ci
          for ( x, y, bv, tr) in ri.tGen( plusOneIfMirrored=True):
            anchor = bv.var( self.idx( x, y))              
            for (f,v) in inst.template.terminals.items():
              a = inst.fa_map[f]
              for term in v:
                for yy in range(term.lly, term.ury):
                  newterm = Rect( term.llx, yy, term.urx, yy+1)
                  r = tr.hitRect( newterm).canonical()
                  if 0 <= r.llx and r.llx < self.nx+1 and 0 <= r.lly and r.lly < self.ny:
                    self.s.emit_implies( anchor, self.net_bvs[a].var( self.idx( r.llx, r.lly)))

        for x in range(self.nx+1):
          for y in range(self.ny):
            vector = [ bv.var( self.idx( x, y)) for (k,bv) in self.net_bvs.items()]
            self.s.emit_at_most_one( vector)


    def addNetLengthConstraints( self, net_nm):
      """
Compute extent of net net_nm in X
Returns a pair (bitvector of net extent and bitvector of tallys)
Use tallys to constrain length
"""

      bv = self.net_bvs[net_nm]
      col_or = tally.BitVec( self.s, 'col_or_%s' % net_nm, self.nx+1)

      nx = self.nx

      for x in range(nx+1):
        self.s.emit_or( [ bv.var( self.idx( x, y)) for y in range(self.ny)], col_or.var( x))

      lscan = tally.BitVec( self.s, 'lscan_%s' % net_nm, nx+1)
      for x in range(nx+1):
        if x == 0:
          self.s.emit_or( [col_or.var( x)], lscan.var( x))
        else:
          self.s.emit_or( [col_or.var( x), lscan.var( x-1)], lscan.var( x))

      rscan = tally.BitVec( self.s, 'rscan_%s' % net_nm, nx+1)
      for x in range(nx+1):
        if x == 0:
          self.s.emit_or( [col_or.var( nx-x)], rscan.var( nx-x))
        else:
          self.s.emit_or( [col_or.var( nx-x), rscan.var( nx-(x-1))], rscan.var( nx-x))

      extent = tally.BitVec( self.s, 'extent_%s' % net_nm, nx+1)
      for x in range(nx+1):
        self.s.emit_and( [lscan.var(x), rscan.var(x)], extent.var( x))

      tallys = tally.BitVec( self.s, 'counts_%s' % net_nm, nx+1)
      self.s.emit_tally( extent.vars, tallys.vars)

      return extent,tallys


    def semantic( self, skipTerminals=False):
        self.ris = [ RasterInstance( self, inst) for inst in self.template.instances.values()]

        for x in range(self.nx):
            for y in range(self.ny):
                self.s.emit_at_most_one( [ri.filled.var( self.idx( x, y)) for ri in self.ris])

        self.nets = OrderedDict()
        for ri in self.ris:
          inst = ri.ci
          for (f,v) in inst.template.terminals.items():
            a = inst.fa_map[f]
            if a not in self.nets: self.nets[a] = []
            self.nets[a].append( (inst,f))

        if not skipTerminals:
          self.addTerminalOverlapConstraints()
          self.xExtents = {}
          for (k,v) in self.nets.items():
            self.xExtents[k] = self.addNetLengthConstraints( k)

        
    def solve( self):
        print( 'Solving Raster')
        self.s.solve()
        assert self.s.state == 'SAT'

        for ri in self.ris:
            ri.backannotatePlacement()

        for ri in self.ris:
            self.print_rasters( ri.anchor)
            self.print_rasters( ri.anchorMY)
            self.print_rasters( ri.anchorMX)
            self.print_rasters( ri.anchorMXY)
            self.print_rasters( ri.filled)

        for (k,bv) in self.net_bvs.items():
            self.print_rasters( bv, nx=self.nx+1)

    def print_rasters( self, bv, nx=None):
        if nx is None: nx = self.nx
        print( bv)
        for y in range(self.ny-1,-1,-1): 
            print( ''.join( [ ('1' if bv.val(self.idx(x,y)) else '0') for x in range(nx)]))


    def optimizeNets( self, priority_nets):
      def findSmallest( net_nm, lst=[]):
        for lim in range(self.nx,-1,-1):
          # if SAT, you can do it in < lim
          self.s.solve( [-self.xExtents[net_nm][1].var( lim)] + lst)
          if self.s.state == 'SAT':
            print( 'Can route %s with < %d x extent' % (net_nm,lim))
          else:
            print( 'Fails to route %s with < %d x extend' % (net_nm,lim))
            return lim


      all_nets = [ x for lst in priority_nets for x in lst]

      limits_independent = []
      for net_nm in all_nets:
        lim = findSmallest( net_nm)
        limits_independent.append( (net_nm, lim))

      limits_sequential2 = []
      accum = []
      for net_nm in all_nets:
        lim = findSmallest( net_nm, accum) + 1
        limits_sequential2.append( (net_nm, lim))
        if lim < self.nx-1:
          accum.append( -self.xExtents[net_nm][1].var( lim))

      self.s.solve( accum)
      assert self.s.state == 'SAT'

      def optimizeNetLength( tag, nets):
        count = 0
        netsInp = []
        for net_nm in nets:
          for x in range(self.nx):
            netsInp.append( self.xExtents[net_nm][0].var( x))
            if self.xExtents[net_nm][0].val( x) is True:
              count += 1
        print( 'Total X length for %s nets' % tag, count)

        netsOut = tally.BitVec( self.s, ('%s X' % tag), count)
        self.s.emit_tally( netsInp, [netsOut.var(x) for x in range(count)])

        for lim in range(count-1,-1,-1):
          # if SAT, you can do it in < lim
          self.s.solve( [-netsOut.var(lim)])
          if self.s.state == 'SAT':
            print( 'Can route %s nets with < %d total x extent' % (tag,lim))
          else:
            print( 'Fails to route %s nets with < %d total x extend' % (tag,lim))
            break
        
        self.s.emit_never( -netsOut.var(lim))
        self.s.solve()
        assert self.s.state == 'SAT'

      for (idx,lst) in enumerate(priority_nets):
        optimizeNetLength( 'priority_%d' % idx, lst)
      
      limits_sequential = []
      for net_nm in all_nets:
        lim = findSmallest( net_nm)
        limits_sequential.append( (net_nm, lim))
        if lim != self.nx:
          self.s.emit_never( self.xExtents[net_nm][1].var( lim+1))

      self.solve()

      print( 'independent', limits_independent)
      print( 'sequential2', limits_sequential2)
      print( 'sequential', limits_sequential)



def test_build_raster():
    s = tally.Tally()
    raster = Raster( s, 'xy', 4, 10)

    s.solve()
    assert s.state == 'SAT'

def test_flat_hier():

    l = CellLeaf( "ndev")
    l.addTerminal( "sd0", Rect(0,0,0,1))
    l.addTerminal( "sd1", Rect(1,0,1,1))

    h = CellHier( "flat")

    nx = 20
    ny = 10

    for x in range(nx):
      for y in range(ny):
        inst_name = 'u_%d_%d' % (x,y)
        h.addInstance( CellInstance( inst_name, l))
        h.instances[inst_name].fa_map['sd0'] = 'a_%d_%d' % (x+1,y)
        h.instances[inst_name].fa_map['sd1'] = 'a_%d_%d' % (x+0,y)

    s = tally.Tally()
    r = Raster( s, h, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}
    for x in range(nx):
      for y in range(ny):
        inst_name = 'u_%d_%d' % (x,y)
        for xx in range(nx):
          for yy in range(ny):
#            s.emit_never( ri_map[inst_name].anchor.var(    r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMY.var(  r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMX.var(  r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMXY.var( r.idx( xx, yy)))

    for y in range(ny):
      for x in range(nx):
        inst_name = 'u_%d_%d' % (x,y)
        s.emit_always( ri_map[inst_name].anchor.var( r.idx( nx-1-x, y)))

    r.solve()
    h.updateBbox()
        
    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        h.write_globalrouting_json( fp, tech)

def test_grid_hier():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b1 = CellLeaf( "block1", Rect(0,0,2,4))

    m = 4

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    for i in range(m):
      inst_name = 'v%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b1)

    nx = 9
    ny = 9

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()
    r.solve()
    g.updateBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)

def test_hier():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b0.addTerminal( "l0", Rect(0,0,0,1))
    b0.addTerminal( "l1", Rect(0,1,0,2))
    b0.addTerminal( "r0", Rect(4,0,4,1))
    b0.addTerminal( "r1", Rect(4,1,4,2))

    m = 2

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    g.instances['u0'].fa_map['l0'] = 'a'
    g.instances['u0'].fa_map['l1'] = 'b'
    g.instances['u0'].fa_map['r0'] = 'c'
    g.instances['u0'].fa_map['r1'] = 'd'

    g.instances['u1'].fa_map['l0'] = 'a'
    g.instances['u1'].fa_map['l1'] = 'b'
    g.instances['u1'].fa_map['r0'] = 'd'
    g.instances['u1'].fa_map['r1'] = 'c'

    nx = 8
    ny = 2

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}

    #place in corner
    s.emit_always( ri_map['u0'].anchor.var( r.idx( 0, 0)))

    r.solve()
    g.updateBbox()

    assert ri_map['u1'].anchorMXY.val( r.idx(nx-1,ny-1)) is True

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)

def test_non_unit_pins():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b0.addTerminal( "l", Rect(0,0,0,2))
    b0.addTerminal( "r", Rect(4,0,4,2))

    m = 2

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    g.instances['u0'].fa_map['l'] = 'a'
    g.instances['u0'].fa_map['r'] = 'b'

    g.instances['u1'].fa_map['l'] = 'b'
    g.instances['u1'].fa_map['r'] = 'c'

    nx = 8
    ny = 2

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}

    #place in corner
    s.emit_always( ri_map['u0'].anchor.var( r.idx( 0, 0)))

    for x in range(nx):
      for y in range(ny):
        pass
        s.emit_never( ri_map['u1'].anchor.var( r.idx( x, y)))
#        s.emit_never( ri_map['u1'].anchorMX.var( r.idx( x, y)))
        s.emit_never( ri_map['u1'].anchorMY.var( r.idx( x, y)))
        s.emit_never( ri_map['u1'].anchorMXY.var( r.idx( x, y)))

    r.solve()
    g.updateBbox()

    assert ri_map['u1'].anchorMX.val( r.idx(4,1)) is True

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)

def test_ota():

    ndual = CellLeaf( "ndual", Rect(0,0,5,2))
    ndual.addTerminal( "d1", Rect(0,0,0,2))
    ndual.addTerminal( "g1", Rect(1,0,1,2))
    ndual.addTerminal( "s1", Rect(2,0,2,2))
    ndual.addTerminal( "s2", Rect(3,0,3,2))
    ndual.addTerminal( "g2", Rect(4,0,4,2))
    ndual.addTerminal( "d2", Rect(5,0,5,2))

    ndualss = CellLeaf( "ndualss", Rect(0,0,4,2))
    ndualss.addTerminal( "d1", Rect(0,0,0,2))
    ndualss.addTerminal( "g1", Rect(1,0,1,2))
    ndualss.addTerminal( "s",  Rect(2,0,2,2))
    ndualss.addTerminal( "g2", Rect(3,0,3,2))
    ndualss.addTerminal( "d2", Rect(4,0,4,2))

    ncap = CellLeaf( "ncap", Rect(0,0,4,2))
    ncap.addTerminal( "d1", Rect(0,0,0,2))
    ncap.addTerminal( "s",  Rect(2,0,2,2))
    ncap.addTerminal( "d2", Rect(4,0,4,2))

    ota = CellHier( "ota")

    ota.addInstance( CellInstance( "L1_MM4_MM3", ncap))
    ota.addInstance( CellInstance( "L1_MM1_MM0", ndualss))

    ota.addInstance( CellInstance( "L1_MM9_MM8", ndual))
    ota.addInstance( CellInstance( "L1_MM7_MM6", ndual))
    ota.addInstance( CellInstance( "L1_MM10_MM2", ndual))

    ota.connect('L1_MM1_MM0','g1','Vinp')

    ota.connect('L1_MM7_MM6','s1','net13')
    ota.connect('L1_MM9_MM8','d1','net13')

    ota.connect('L1_MM7_MM6','d2','Voutp')
    ota.connect('L1_MM10_MM2','d2','Voutp')

    ota.connect('L1_MM7_MM6','d1','Voutn')
    ota.connect('L1_MM10_MM2','d1','Voutn')

    ota.connect('L1_MM10_MM2','s1','net10')
    ota.connect('L1_MM1_MM0','d1','net10')

    ota.connect('L1_MM9_MM8','s1','vdd!')
    ota.connect('L1_MM9_MM8','s2','vdd!')

    ota.connect('L1_MM10_MM2','g1','Vbiasn')
    ota.connect('L1_MM10_MM2','g2','Vbiasn')

    ota.connect('L1_MM10_MM2','s2','net11')
    ota.connect('L1_MM1_MM0','d2','net11')
    
    ota.connect('L1_MM9_MM8','g1','Vbiasp2')
    ota.connect('L1_MM9_MM8','g2','Vbiasp2')

    ota.connect('L1_MM7_MM6','g1','Vbiasp1')
    ota.connect('L1_MM7_MM6','g2','Vbiasp1')

    ota.connect('L1_MM4_MM3','s','gnd!')

    ota.connect('L1_MM7_MM6','s2','net12')
    ota.connect('L1_MM9_MM8','d2','net12')

    ota.connect('L1_MM1_MM0','s','net6')
    ota.connect('L1_MM4_MM3','d2','net6')

    ota.connect('L1_MM1_MM0','g2','Vinn')
 
    ota.connect('L1_MM4_MM3','d1','net1')

    nx = 13
    ny = 6

    ota.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, ota, nx, ny)
    r.semantic()

    #put a raft on the left and right
    for x in [0,nx-1]:
      for y in range(ny):
        for ri in r.ris:
          print( ri.ci.nm, x, y)
          s.emit_never( ri.filled.var( r.idx( x, y)))

    s.solve()
    assert s.state == 'SAT'

    priority_nets = ['net6', 'Vbiasn', 'Vbiasp1', 'Vbiasp2', 'Voutn', 'Voutp', 'net12', 'net13']
    other_nets = [ n for n in r.nets.keys() if n not in priority_nets]
    r.optimizeNets( [priority_nets,other_nets])

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        ota.write_globalrouting_json( fp, tech)

    with open( "ota_placer_out.json", "wt") as fp:
        tech = Tech()
        ota.dumpJson( fp, tech)

def test_sc():

    ndev = CellLeaf( "ndev", Rect(0,0,2,2))
    ndev.addTerminal( "d", Rect(0,0,0,2))
    ndev.addTerminal( "g", Rect(1,0,1,2))
    ndev.addTerminal( "s", Rect(2,0,2,2))

    cc = CellLeaf( "cc", Rect(0,0,3,2))
    cc.addTerminal( "cp1", Rect(0,0,0,2))
    cc.addTerminal( "cn1", Rect(1,0,1,2))
    cc.addTerminal( "cn2", Rect(2,0,2,2))
    cc.addTerminal( "cp2", Rect(3,0,3,2))

    ccbig = CellLeaf( "ccbig", Rect(0,0,5,2))
    ccbig.addTerminal( "cp1", Rect(0,0,0,2))
    ccbig.addTerminal( "cn1", Rect(1,0,1,2))
    ccbig.addTerminal( "cn2", Rect(4,0,4,2))
    ccbig.addTerminal( "cp2", Rect(5,0,5,2))

    sc = CellHier( "sc")

    sc.addInstance( CellInstance( "L0_MM0", ndev))
    sc.addInstance( CellInstance( "L0_MM1", ndev))
    sc.addInstance( CellInstance( "L0_MM2", ndev))
    sc.addInstance( CellInstance( "L0_MM3", ndev))
    sc.addInstance( CellInstance( "L0_MM4", ndev))
    sc.addInstance( CellInstance( "L0_MM5", ndev))
    sc.addInstance( CellInstance( "L0_MM6", ndev))
    sc.addInstance( CellInstance( "L0_MM7", ndev))
    sc.addInstance( CellInstance( "L0_MM8", ndev))

    sc.addInstance( CellInstance( "L0_MM9", ndev))
    sc.addInstance( CellInstance( "L0_MM10", ndev))
    sc.addInstance( CellInstance( "L0_MM11", ndev))

    sc.addInstance( CellInstance( "L1_CC5_CC7", cc))
    sc.addInstance( CellInstance( "L1_CC4_CC6", ccbig))
    sc.addInstance( CellInstance( "L1_CC1_CC3", ccbig))
    sc.addInstance( CellInstance( "L1_CC0_CC2", ccbig))

    sc.connect( 'L1_CC5_CC7', 'cp1', 'net23')
    sc.connect( 'L1_CC0_CC2', 'cp1', 'net23')
    sc.connect( 'L0_MM1', 's', 'net23')
#    sc.connect( 'I0', 'Vinn', 'net23')

    sc.connect( 'L0_MM0', 's', 'net3')
    sc.connect( 'L0_MM10', 's', 'net3')
    sc.connect( 'L1_CC4_CC6', 'cn1', 'net3')

    sc.connect( 'L0_MM11', 's', 'net12')
    sc.connect( 'L0_MM8', 'd', 'net12')
    sc.connect( 'L1_CC1_CC3', 'cn2', 'net12')

    sc.connect( 'L0_MM3', 'd', 'net7')
    sc.connect( 'L1_CC5_CC7', 'cp2', 'net7')
    sc.connect( 'L1_CC0_CC2', 'cp2', 'net7')
#    sc.connect( 'I0', 'Vinp', 'net7')

    sc.connect( 'L0_MM5', 'd', 'net5')
    sc.connect( 'L0_MM3', 's', 'net5')
    sc.connect( 'L1_CC4_CC6', 'cp2', 'net5')
    sc.connect( 'L1_CC1_CC3', 'cp1', 'net5')

    sc.connect( 'L0_MM9', 's', 'net6')
    sc.connect( 'L0_MM1', 'd', 'net6')
    sc.connect( 'L1_CC4_CC6', 'cp1', 'net6')
    sc.connect( 'L1_CC1_CC3', 'cp2', 'net6')

#    sc.connect( 'terminal Vbiasn', 'Vbiasn')
#    sc.connect( 'I0', 'Vbiasn', 'Vbiasn')

#    sc.connect( 'terminal Vbiasp1', 'Vbiasp1')
#    sc.connect( 'I0', 'Vbiasp1', 'Vbiasp1')

#    sc.connect( 'terminal Vbiasp2', 'Vbiasp2')
#    sc.connect( 'I0', 'Vbiasp2', 'Vbiasp2')

    sc.connect( 'L0_MM2', 's', 'Vinn')
    sc.connect( 'L1_CC5_CC7', 'cn1', 'Vinn')
#    sc.connect( 'terminal Vinn', 'Vinn')

    sc.connect( 'L0_MM0', 'd', 'Vinp')
    sc.connect( 'L1_CC5_CC7', 'cn2', 'Vinp')
#    sc.connect( 'terminal Vinp', 'Vinp')

    sc.connect( 'L0_MM7', 'd', 'Voutn')
    sc.connect( 'L1_CC0_CC2', 'cn2', 'Voutn')
#    sc.connect( 'I0', 'Voutn', 'Voutn')
#    sc.connect( 'terminal Voutn', 'Voutn')

    sc.connect( 'L0_MM8', 's', 'Voutp')
    sc.connect( 'L1_CC0_CC2',  'cn1', 'Voutp')
#    sc.connect( 'I0', 'Voutp', 'Voutp')
#    sc.connect( 'terminal Voutp', 'Voutp')

    sc.connect( 'L0_MM11', 'g', 'phi1')
    sc.connect( 'L0_MM6', 'g', 'phi1')
    sc.connect( 'L0_MM1', 'g', 'phi1')
    sc.connect( 'L0_MM3', 'g', 'phi1')
    sc.connect( 'L0_MM0', 'g', 'phi1')
    sc.connect( 'L0_MM2', 'g', 'phi1')
#    sc.connect( 'terminal phi1', 'phi1')

    sc.connect( 'L0_MM2', 'd', 'net4')
    sc.connect( 'L0_MM4', 'd', 'net4')
    sc.connect( 'L1_CC4_CC6', 'cn2', 'net4')

    sc.connect( 'L0_MM8', 'g', 'phi2')
    sc.connect( 'L0_MM7', 'g', 'phi2')
    sc.connect( 'L0_MM9', 'g', 'phi2')
    sc.connect( 'L0_MM5', 'g', 'phi2')
    sc.connect( 'L0_MM4', 'g', 'phi2')
    sc.connect( 'L0_MM10', 'g', 'phi2')
#    sc.connect( 'terminal phi2', 'phi2')

#    sc.connect( 'I0', 'vdd!', 'vdd!')
#    sc.connect( 'terminal vdd!', 'vdd!')

#    sc.connect( 'terminal Id', 'Id')
#    sc.connect( 'I0', 'Id', 'Id')

    sc.connect( 'L0_MM11', 'd', 'gnd!')
    sc.connect( 'L0_MM6', 's', 'gnd!')
    sc.connect( 'L0_MM9', 'd', 'gnd!')
    sc.connect( 'L0_MM5', 's', 'gnd!')
    sc.connect( 'L0_MM4', 's', 'gnd!')
    sc.connect( 'L0_MM10', 'd', 'gnd!')
#    sc.connect( 'I0', 'gnd!', 'gnd!')
#    sc.connect( 'terminal gnd!', 'gnd!')

    sc.connect( 'L0_MM6', 'd', 'net11')
    sc.connect( 'L0_MM7', 's', 'net11')
    sc.connect( 'L1_CC1_CC3', 'cn1', 'net11')

    nx = 16
    ny = 10

    sc.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, sc, nx, ny)
    r.semantic( skipTerminals=False)

    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          s.emit_never( ri.anchorMX.var( r.idx( x,y)))
          s.emit_never( ri.anchorMY.var( r.idx( x,y)))
          s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    #put a raft on the left and right
    for x in [0,nx-1]:
      for y in range(ny):
        for ri in r.ris:
          print( ri.ci.nm, x, y)
          s.emit_never( ri.filled.var( r.idx( x, y)))

    print( "First solve")
    s.solve()
    assert s.state == 'SAT'

    priority_nets = ['net7','net23']
    remaining_nets = [ n for n in r.nets.keys() if n not in priority_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [ list(tup) for tup in chunk( remaining_nets, 6)]

    r.optimizeNets( [priority_nets] + groups)

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        sc.write_globalrouting_json( fp, tech)

    with open( "sc_placer_out.json", "wt") as fp:
        tech = Tech()
        sc.dumpJson( fp, tech)

if __name__ == "__main__":
#  test_grid_hier()
#  test_flat_hier()
#  test_hier()
  test_sc()
#  test_ota()
#  test_non_unit_pins()

