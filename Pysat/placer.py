#!/usr/bin/env python

import pytest
import tally
import json

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

def encode_T( tech, obj):
  if isinstance(obj, Rect):
    r = Rect()
    r.llx = tech.pitchPoly*tech.halfXADTGrid*2*obj.llx
    r.urx = tech.pitchPoly*tech.halfXADTGrid*2*obj.urx
    r.lly = tech.pitchDG  *tech.halfYADTGrid*2*obj.lly
    r.ury = tech.pitchDG  *tech.halfYADTGrid*2*obj.ury 
    return r.toList()
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

class CellTemplate:
    def __init__( self, nm):
        self.nm = nm
        
    def __repr__( self):
        return "CellTemplate(" + nm + "," + self.instances + "," + self.bbox + ")"

    def write_globalrouting_json( self, fp, tech):
        grs = []
        terminals = []

        terminals.append( { "netName" : self.nm, "layer" : "diearea", "rect" : self.bbox})
        for inst in self.instances:
            r = inst.transformation.hitRect( inst.template.bbox)
            nm = self.nm + '/' + inst.nm
            terminals.append( { "netName" : nm, "layer" : "cellarea", "rect" : r.canonical()})

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
        return []

    @property
    def bbox( self):
        return Rect(0,0,1,1)

class CellHier(CellTemplate):
    def __init__( self, nm):
        super().__init__(nm)
        self.instances = []
        self.bbox = None

class CellInstance:
    def __init__( self, nm, template, trans):
        self.nm = nm
        self.template = template
        self.transformation = trans

class Raster:
    def __init__( self, s, nm, nx, ny):
        self.nx = nx
        self.ny = ny
        self.bv = tally.BitVec( s, 'nm', nx*ny)

    def idx( x, y):
        return x*ny + y



def test_build_raster():
    s = tally.Tally()
    raster = Raster( s, 'xy', 4, 10)

    s.solve()
    assert s.state == 'SAT'

def test_simple_hier():

    l = CellLeaf( "ndev")
    h = CellHier( "npair")

    h.instances.append( CellInstance( 'u0', l, Transformation(0,0)))
    h.instances.append( CellInstance( 'u1', l, Transformation(1,0)))
    h.bbox = Rect(0,0,2,1)

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        h.write_globalrouting_json( fp, tech)

if __name__ == "__main__":
    test_simple_hier()
