#!/usr/bin/env python

import tally
import json
from collections import defaultdict
from collections import OrderedDict

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
    def __init__( self, oX=0, oY = 0, sX=1, sY=1):
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

    def preMult( self, A):
        # A            self
        # sx 0  ox     sx 0  ox
        # 0  sy oy     0  sy oy   
        # 0  0  1      0  0  1
        C = Transformation()
        C.sX = A.sX * self.sX
        C.sY = A.sY * self.sY
        C.oX = A.sX * self.oX + A.oX
        C.oY = A.sY * self.oY + A.oY
        return C

    def postMult( self, A):
        # self         A
        # sx 0  ox     sx 0  ox
        # 0  sy oy     0  sy oy   
        # 0  0  1      0  0  1
        C = Transformation()
        C.sX = self.sX * A.sX
        C.sY = self.sY * A.sY
        C.oX = self.sX * A.oX + self.oX
        C.oY = self.sY * A.oY + self.oY
        return C

def test_transformation_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_transformation_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

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
      r.lly = tech.pitchDG  *tech.halfYADTGrid*2*obj.r.lly + 200
      r.ury = tech.pitchDG  *tech.halfYADTGrid*2*obj.r.ury - 200
      return { "netName" : obj.nm, "layer" : obj.layer, "rect" : r.toList()}
    else:
      raise TypeError(repr(obj) + (" is not JSON serializable. Unknown terminal layer %s" % obj.layer))
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

class CellTemplate:
    def __init__( self, nm):
        self.nm = nm
        self.terminals = OrderedDict()
        
    def addInstance( self, ci):
        self.instances[ci.nm] = ci

    def addTerminal( self, nm, r):
        if nm not in self.terminals: self.terminals[nm] = []
        assert r.llx     == r.urx
        assert r.lly + 1 == r.ury
        self.terminals[nm].append( r)

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
    def __init__( self, nm):
        super().__init__(nm)

    @property
    def instances( self):
        return OrderedDict()

    @property
    def bbox( self):
        return Rect(0,0,1,1)

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
    def __init__( self, nm, template, trans):
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

    def tGen( self):
        for x in range(self.r.nx):
            for y in range(self.r.ny):
              pairs = [( self.anchor,    Transformation( x, y,  1,  1)),
                       ( self.anchorMY,  Transformation( x, y, -1,  1)),
                       ( self.anchorMX,  Transformation( x, y,  1, -1)),
                       ( self.anchorMXY, Transformation( x, y, -1, -1))]
              for ( bv, tr) in pairs:
                yield ( x, y, bv, tr)

    def backannotatePlacement( self):
      self.ci.transformation = None
      for ( x, y, bv, tr) in self.tGen():
        if bv.val( self.r.idx( x, y)) is True:
          if tr.sX == -1: tr.oX += 1
          if tr.sY == -1: tr.oY += 1
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

    def addNetConstraints( self):
        nets = OrderedDict()
        for ri in self.ris:
          inst = ri.ci
          for (f,v) in inst.template.terminals.items():
            a = inst.fa_map[f]
            if a not in nets: nets[a] = []
            nets[a].append( (inst,f))

        print( "Building bit vectors for %d nets" % len(nets))

        self.net_bvs = OrderedDict()
        for k in nets.keys():
          self.net_bvs[k] = tally.BitVec( self.s, ('net_terminal_%s' % k), (self.nx+1)*self.ny)

        for ri in self.ris:
          inst = ri.ci
          for ( x, y, bv, tr) in ri.tGen():
            if tr.sX < 0: tr.oX += 1
            if tr.sY < 0: tr.oY += 1
            anchor = bv.var( self.idx( x, y))              
            for (f,v) in inst.template.terminals.items():
              a = inst.fa_map[f]
              for term in v:
                r = tr.hitRect( term).canonical()
                if 0 <= r.llx and r.llx < self.nx+1 and 0 <= r.lly and r.lly < self.ny:
                  self.s.emit_implies( anchor, self.net_bvs[a].var( self.idx( r.llx, r.lly)))

        for x in range(self.nx+1):
          for y in range(self.ny):
            vector = [ bv.var( self.idx( x, y)) for (k,bv) in self.net_bvs.items()]
            self.s.emit_at_most_one( vector)


    def semantic( self):
        self.ris = [ RasterInstance( self, inst) for inst in self.template.instances.values()]

        for x in range(self.nx):
            for y in range(self.ny):
                self.s.emit_at_most_one( [ri.filled.var( self.idx( x, y)) for ri in self.ris])

        self.addNetConstraints()

        
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
        h.addInstance( CellInstance( inst_name, l, Transformation(0,0)))
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

    l = CellLeaf( "ndev")
    l.addTerminal( "sd0", Rect(0,0,0,1))
    l.addTerminal( "sd1", Rect(1,0,1,1))

    b0 = CellHier( "block0")
    b0.addInstance( CellInstance( 'u0', l, Transformation(0,0)))
    b0.addInstance( CellInstance( 'u1', l, Transformation(4,2,-1,-1)))
    b0.updateBbox()

    b1 = CellHier( "block1")
    b1.addInstance( CellInstance( 'u0', l, Transformation(0,0)))
    b1.addInstance( CellInstance( 'u1', l, Transformation(2,4,-1,-1)))
    b1.updateBbox()

    m = 4

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0, Transformation(0,0))

    for i in range(m):
      inst_name = 'v%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b1, Transformation(0,0))

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

if __name__ == "__main__":
    test_flat_hier()
    test_grid_hier()
