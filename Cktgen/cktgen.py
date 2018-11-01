
import argparse
import pathlib
from collections import OrderedDict

import json

import techfile

class ADT:
  def __init__( self, tech, nm, npp=10, nr=1):
    self.tech = tech
    self.nm = nm
    self.bbox = Rect( 0, 0, npp*self.tech.pitchPoly, nr*self.tech.dgPerRow*self.tech.pitchDG)
    self.terminals = []

  @property
  def nrows( self):
    """Computes number of ADT row heights.
"""
    dy = self.bbox.ury-self.bbox.lly
    assert dy % (self.tech.dgPerRow*self.tech.pitchDG) == 0
    return dy // (self.tech.dgPerRow*self.tech.pitchDG)

  @property
  def npps( self):
    """Computes number of poly pitches.
"""
    dx = self.bbox.urx-self.bbox.llx
    assert dx % self.tech.pitchDG == 0
    return dx // self.tech.pitchDG

  def newWire( self, netName, rect, layer):
    w = Wire()
    w.netName = netName
    w.rect = rect
    w.layer = layer
    w.gid = -1
    self.terminals.append( w)
    return w

  def addM1Terminal( self, netName, m1TracksOffset):
    """Add a m1 terminal (vertical) that spans the entire ADT and is centered on track m1TracksOffset (zero is the left boundary of the cell.)
"""
    xc = self.tech.pitchM1*m1TracksOffset
    return self.newWire( netName, Rect( xc-self.tech.halfWidthM1[0], self.bbox.lly+self.tech.halfMinETESpaceM1, xc+self.tech.halfWidthM1[0], self.bbox.ury-self.tech.halfMinETESpaceM1), "metal1")

  def __repr__( self):
    return self.nm + "," + str(self.bbox) + "," + str(self.terminals)

  @staticmethod
  def parse_lgf( tech, fn):

    p_cell = re.compile( r'^Cell\s+(\S+)\s+bbox=(\S+):(\S+):(\S+):(\S+)\s*$')
    p_wire = re.compile( r'^Wire\s+net=(\S+)\s+(gid=(\S+)\s+|)layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)\s*$')
    p_obj = re.compile( r'^Obj\s+net=(\S+)\s+gen=(\S+)\s+x=(\S+)\s+y=(\S+)\s*$')
    p_space = re.compile( r'^\s*$')
    p_comment = re.compile( r'^#.*$')

    with open( fn, "r") as fp:
      adt = None

      for line in fp:
        line = line.rstrip( '\n')
      
        m = p_cell.match( line)
        if m:
          cell = m.groups()[0]
          bbox = Rect( int(m.groups()[1]), int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]))

          adt = ADT( d, cell)
          adt.bbox = bbox
          continue

        m = p_wire.match( line)
        if m:
          net = m.groups()[0]
          gid = m.groups()[2]
          if gid is not None: gid = int(gid)
          layer = m.groups()[3]        
          rect = Rect( int(m.groups()[4]), int(m.groups()[5]), int(m.groups()[6]), int(m.groups()[7]))

          if True or layer in ["metalc2", "metal2"]:
            w = adt.newWire( net, rect, layer)
            w.gid = gid
            print( w)
          continue

        m = p_obj.match( line)
        if m:
          net = m.groups()[0]
          gen = m.groups()[1]
          x = int(m.groups()[2])
          y = int(m.groups()[3])
          continue

        m = p_space.match( line)
        if m: continue

        m = p_comment.match( line)
        if m: continue

        assert False, line

      return adt

class ADITransform:
  @staticmethod
  def translate( tx, ty):
    trans = ADITransform()
    trans.xOffset = tx
    trans.yOffset = ty
    return trans

  @staticmethod
  def mirrorAcrossXAxis():
    trans = ADITransform()
    trans.yScale = -1
    return trans

  @staticmethod
  def mirrorAcrossYAxis():
    trans = ADITransform()
    trans.xScale = -1
    return trans

  def __init__( self, oX=0, oY=0, sX=1, sY=1):
    self.xOffset = oX
    self.yOffset = oY
    self.xScale = sX
    self.yScale = sY

  def __repr__( self):
    return "xo yo xs ys: %d %d %d %d" % ( self.xOffset, self.yOffset, self.xScale, self.yScale)

  def copy( self):
    R = ADITransform()
    R.xOffset = self.xOffset
    R.yOffset = self.yOffset
    R.xScale = self.xScale
    R.yScale = self.yScale
    return R

  def hit( self, p):
    ( x, y) = p
    return ( self.xScale * x + self.xOffset, self.yScale * y + self.yOffset)

  def preMult( self, A):
# sx 0  tx
# 0  sy ty
# 0  0  1
    C = ADITransform()
    C.xOffset = A.xScale * self.xOffset + A.xOffset
    C.yOffset = A.yScale * self.yOffset + A.yOffset
    C.xScale = A.xScale * self.xScale
    C.yScale = A.yScale * self.yScale
    return C

class TestADITransform:
  def test_hit0( self):
    trans = ADITransform()
    assert (0,0) == trans.hit( (0,0))
  def test_hit1( self):
    trans = ADITransform()
    assert (100,50) == trans.hit( (100,50))
  def test_hit2( self):
    trans = ADITransform.translate( 100, -50)
    assert (200,0) == trans.hit( (100,50))
  def test_hit3( self):
    trans = ADITransform.mirrorAcrossXAxis()
    assert (100,-50) == trans.hit( (100,50))
  def test_hit4( self):
    trans = ADITransform.mirrorAcrossYAxis()
    assert (-100,50) == trans.hit( (100,50))
  def test_preMult0( self):
    trans0 = ADITransform.mirrorAcrossYAxis()
    trans1 = ADITransform.translate( 100, -50)
    trans = trans1.preMult(trans0)
    pt = (100,50)
    assert trans.hit( pt) == trans0.hit( trans1.hit( pt))
  def test_preMult0( self):
    trans0 = ADITransform.mirrorAcrossXAxis()
    trans1 = ADITransform.translate( 100, -50)
    trans = trans1.preMult(trans0)
    pt = (100,50)
    assert trans.hit( pt) == trans0.hit( trans1.hit( pt))


class ADI:
  def __init__( self, t, iName, trans=None):
    self.template = t
    self.instanceName = iName
    self.formalActualMap = OrderedDict()
    if trans is None:
      self.trans = ADITransform()
    else:
      self.trans = trans

  def __repr__( self):
    return "template: %s instance: %s trans: %s" % (self.template, self.instanceName, self.trans)

  def hit( self, r):
    (llx,lly) = self.trans.hit( (r.llx, r.lly))
    (urx,ury) = self.trans.hit( (r.urx, r.ury))
    if ( llx > urx): llx, urx = urx, llx
    if ( lly > ury): lly, ury = ury, lly
    return Rect( llx, lly, urx, ury)

  @property
  def bbox( self):
    return self.hit( self.template.bbox)

class ADNetlist:
  def __init__( self, nm):
    self.nm = nm
    self.instances = OrderedDict()
    self.nets = OrderedDict()

  def addInstance( self, i):
    self.instances[i.instanceName] = i

  def connect( self, instanceName, f, a):
    if a not in self.nets:
      self.nets[a] = []
    self.nets[a].append( (instanceName,f))
    self.instances[instanceName].formalActualMap[f] = a

  def genNetlist( self, netl):
    for (k,v) in self.instances.items():
      print( "templateName", v.template.nm, "instanceName", v.instanceName)
      netl.instances[v.instanceName] = v.bbox

      for w in v.template.terminals:
        a = "!kor" if w.netName not in v.formalActualMap else v.formalActualMap[w.netName]
        if True or a not in ["vcc","vss"]:
          netl.newWire( a, v.hit( w.rect), w.layer)
          print( "genNetlist", w)


class Rect:
  def __init__( self, llx, lly, urx=None, ury=None):
    self.llx = llx
    self.lly = lly
    self.urx = llx if urx is None else urx
    self.ury = lly if ury is None else ury

  def __str__( self):
    return "%d:%d:%d:%d" % (self.llx,self.lly,self.urx,self.ury)

  def __repr__( self):
    return str(self)

  def add( self, x, y):
    return Rect( min(x,self.llx), min(y,self.lly), max(x,self.urx), max(y,self.ury))

  def canonical( self):
    llx,lly,urx,ury = self.llx,self.lly,self.urx,self.ury
    if llx > urx: llx,urx = urx,llx
    if lly > ury: lly,ury = ury,lly
    return Rect( llx,lly,urx,ury)

  def toList( self):
    return [self.llx,self.lly,self.urx,self.ury]

class Wire:
  def __init__( self):
    self.netName = None
    self.rect = None
    self.layer = None
    self.gid = None

  def __str__( self):
    return "Wire  net=%s%s layer=%s rect=%s" % ( self.netName, ("" if self.gid is None else ( " gid=%d" % self.gid)), self.layer, self.rect)

  def __repr__( self):
    return str(self)

class GR:
  def __init__( self):
    self.netName = None
    self.rect = None
    self.layer = None
    self.width = None

def encode_GR( tech, obj):
  if isinstance(obj, GR):
# Convert global route coords to physical coords
    if obj.rect.llx == obj.rect.urx: # vertical wire
      xc = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.llx + tech.halfXGRGrid)
      llx = xc - obj.width//2
      urx = xc + obj.width//2
      lly = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.lly + tech.halfYGRGrid)
      ury = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.ury + tech.halfYGRGrid)
    elif obj.rect.lly == obj.rect.ury: # horizontal wire
      yc = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.lly + tech.halfYGRGrid)
      lly = yc - obj.width//2
      ury = yc + obj.width//2
      llx = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.llx + tech.halfXGRGrid)
      urx = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.urx + tech.halfXGRGrid)
    else:
      raise RuntimeError(repr(obj) + "is not horizontal nor vertical.")

    return { "netName" : obj.netName, "layer" : obj.layer, "width" : obj.width, "rect" : [llx, lly, urx, ury]}
  elif isinstance(obj, Wire):
    return { "netName" : obj.netName, "layer" : obj.layer, "gid" : obj.gid, "rect" : [obj.rect.llx, obj.rect.lly, obj.rect.urx, obj.rect.ury]}
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

class Net:
  def __init__( self, nm):
    self.nm = nm
    self.wires = []
    self.grs = []

class Netlist:
  def __init__( self, nm, bbox):
    self.nm = nm
    self.bbox = bbox
    self.nets = OrderedDict()
    self.gidIndex = 0
    self.instances = OrderedDict()
    self.wires = {}

  def dumpGR( self, tech, fn):
    with open( fn, "w") as fp:
# mimic what flatmap would do
      grs = []
      terminals = []

      wire = Wire()
      wire.netName = 'top'
      wire.rect = self.bbox
      wire.layer = 'diearea'
      wire.gid = -1
      terminals.append( wire)

      for (instanceName, rect) in self.instances.items():
        wire = Wire()
        wire.netName = instanceName
        wire.rect = rect
        wire.layer = 'cellarea'
        wire.gid = -1
        terminals.append( wire)

      for (netName,net) in self.nets.items():
        for gr in net.grs:
          grs.append(gr)
        for wire in net.wires:
          terminals.append( wire)

      grGrid = []
      dx = tech.pitchPoly*tech.halfXGRGrid*2
      dy = tech.pitchDG*tech.halfYGRGrid*2
      for x in range( self.bbox.llx, self.bbox.urx, dx):
        for y in range( self.bbox.lly, self.bbox.ury, dy):
          grGrid.append( [x,y,x+dx,y+dy])

      data = { "bbox" : [self.bbox.llx, self.bbox.lly, self.bbox.urx, self.bbox.ury], "globalRoutes" : grs, "globalRouteGrid" : grGrid, "terminals" : terminals}


      fp.write( json.dumps( data, indent=2, default=lambda x: encode_GR(tech,x)) + "\n")

  def newWire( self, netName, r, l):
    cand = (netName, (r.llx, r.lly, r.urx, r.ury), l)
    if cand not in self.wires:
      w = Wire()
      w.netName = netName
      w.rect = r
      w.layer = l
      w.gid = self.gidIndex
      self.gidIndex += 1

      if netName not in self.nets:
        self.nets[netName] = Net( netName)

      self.nets[netName].wires.append( w)
      self.wires[cand] = w
    else:
      w = self.wires[cand]
      
    return w

  def newGR( self, netName, r, l, w):
    gr = GR()

    gr.netName = netName
    gr.layer = l
    gr.rect = r.canonical()
    gr.width = w

    if netName not in self.nets:
      self.nets[netName] = Net( netName)

    self.nets[netName].grs.append( gr)

    return gr

  def write_ctrl_file( self, fn, route, show_global_routes, show_metal_templates):
    with open( fn, "w") as fp:
      fp.write( """# circuit-independent technology collateral
Option name=layer_file          value={4}/layers.txt
Option name=arch_file           value={4}/arch.txt
Option name=generator_file      value={4}/car_generators.txt
Option name=pattern_file        value={4}/v2_patterns.txt
Option name=option_file         value={4}/design_rules.txt

# technology collateral may vary for different circuits
Option name=metal_template_file value=INPUT/{0}_dr_metal_templates.txt

# circuit-specific collateral
Option name=global_routing_file value=INPUT/{0}_dr_globalrouting.txt
Option name=input_file          value=INPUT/{0}_dr_netlist.txt
Option name=option_file         value=INPUT/{0}_dr_mti.txt

# primary synthesis options
Option name=route       value={1}
Option name=solver_type value=glucose
Option name=allow_opens value=1

# custom routing options
#Option name=nets_to_route value=i,o
Option name=nets_not_to_route value=ALS_KOR_DO_NOT_ROUTE,vss,vcc

# debug options
Option name=create_fake_global_routes            value={2}
Option name=create_fake_connected_entities       value=0
Option name=create_fake_ties                     value=0
Option name=create_fake_metal_template_instances value={3}
Option name=create_fake_line_end_grids           value=1
""".format( self.nm,
            "1" if route else "0",
            "1" if show_global_routes else "0",
            "1" if show_metal_templates else "0",
            "DR_COLLATERAL"))

  def write_input_file( self, fn):
    with open( fn, "w") as fp:
      fp.write( "Cell name=%s bbox=%s\n" % (self.nm, self.bbox))
      for (k,v) in self.nets.items():
        for w in v.wires:
          fp.write( str(w) + "\n")

  def write_global_routing_file( self, fn):
    with open( fn, "w") as fp:
      for (k,v) in self.nets.items():
        fp.write( "#start of regular net %s\n" % k)

        for w in v.wires:
          fp.write( "ConnectedEntity terms=%d {\n" % w.gid)
          fp.write( " }\n")
          fp.write( "\n")

        s = ';'.join( ["(%d,%d,%d,%d,%s,minw=%d)" % (gr.rect.llx,
                                                gr.rect.lly,
                                                gr.rect.urx,
                                                gr.rect.ury,
                                                gr.layer,gr.width) for gr in v.grs])
        fp.write( "GlobalRouting net=%s routes=%s\n" % (k,s))

        fp.write( "#end of net %s\n" % k)
      pass

  def write_files( self, tech, dir, args):
    self.write_ctrl_file( dir + "/ctrl.txt", args.route, args.show_global_routes, args.show_metal_templates)
    self.write_input_file( dir + "/" + self.nm + "_dr_netlist.txt")
    self.write_global_routing_file( dir + "/" + self.nm + "_dr_globalrouting.txt")
    self.dumpGR( tech, dir + "/" + self.nm + "_dr_globalrouting.json")


import re

def parse_lgf( fp):

  netl = None

  p_cell = re.compile( r'^Cell\s+(\S+)\s+bbox=(\S+):(\S+):(\S+):(\S+)\s*$')
  p_wire = re.compile( r'^Wire\s+net=(\S+)\s+(gid=(\S+)\s+|)layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)\s*$')

  p_wire2 = re.compile( r'^Wire\s+net=(\S+)\s+layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)(\s+gid=(\S+)|)\s*$')

  p_wire_in_obj = re.compile( r'^\s+Wire\s+net=(\S+)\s+layer=(\S+)\s+rect=(\S+):(\S+):(\S+):(\S+)\s*$')

  p_obj = re.compile( r'^Obj\s+net=(\S+)\s+gen=(\S+)\s+x=(\S+)\s+y=(\S+)\s*$')

  p_obj_lbrace = re.compile( r'^Obj\s+net=(\S+)\s+gen=(\S+)\s+x=(\S+)\s+y=(\S+)\s*{\s*$')

  p_rbrace = re.compile( r'^\s*}\s*$')

  p_space = re.compile( r'^\s*$')

  if True:
    for line in fp:
      line = line.rstrip( '\n')
      
      m = p_cell.match( line)
      if m:
        cell = m.groups()[0]
        bbox = Rect( int(m.groups()[1]), int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]))

        netl = Netlist( cell, bbox)
        continue

      m = p_wire.match( line)
      if m:
        net = m.groups()[0]
        gid = m.groups()[2]
        if gid is not None: gid = int(gid)
        layer = m.groups()[3]        
        rect = Rect( int(m.groups()[4]), int(m.groups()[5]), int(m.groups()[6]), int(m.groups()[7]))

        w = netl.newWire( net, rect, layer)
        w.gid = gid

        continue

      m = p_wire2.match( line)
      if m:
        net = m.groups()[0]
        layer = m.groups()[1]        
        rect = Rect( int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]), int(m.groups()[5]))
        gid = m.groups()[7]
        if gid is not None: gid = int(gid)

        w = netl.newWire( net, rect, layer)
        w.gid = gid

        continue

      m = p_obj.match( line)
      if m:
        net = m.groups()[0]
        gen = m.groups()[1]
        x = int(m.groups()[2])
        y = int(m.groups()[3])
        continue

      m = p_obj_lbrace.match( line)
      if m:
        net = m.groups()[0]
        gen = m.groups()[1]
        x = int(m.groups()[2])
        y = int(m.groups()[3])
        continue

      m = p_wire_in_obj.match( line)
      if m:
        net = m.groups()[0]
        layer = m.groups()[1]        
        rect = Rect( int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]), int(m.groups()[5]))
        continue

      m = p_rbrace.match( line)
      if m:

        continue

      m = p_space.match( line)
      if m: continue

      assert False, line

  return netl

def parse_args():
  parser = argparse.ArgumentParser( description="Generates input files for amsr (Analog router)")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "--route", action='store_true')
  parser.add_argument( "--show_global_routes", action='store_true')
  parser.add_argument( "--show_metal_templates", action='store_true')
  parser.add_argument( "--consume_results", action='store_true')
  parser.add_argument( "-tf", "--technology_file", type=str, default="DR_COLLATERAL/Process.json")

  args = parser.parse_args()

  with open( args.technology_file) as fp:
    tech = techfile.TechFile( fp)

  if args.consume_results:
    with open( 'out/' + args.block_name + '.lgf', 'rt') as fp:  
      netl = parse_lgf( fp)

    netl.write_input_file( netl.nm + "_xxx.txt")
    netl.dumpGR( tech, "INPUT/" + args.block_name + "_dr_globalrouting.json")

    exit()

  return args,tech


if __name__ == "__main__":
  args,tech = parse_args()

  ndev = ADT( tech, "n",npp=6,nr=1)
  ndev.addM1Terminal( "s", 1)
  ndev.addM1Terminal( "g", 3)
  ndev.addM1Terminal( "d", 5)

  pdev = ADT( tech, "p",npp=6,nr=1)
  pdev.addM1Terminal( "s", 1)
  pdev.addM1Terminal( "g", 3)
  pdev.addM1Terminal( "d", 5)

# python cktgen.py --block_name mydesign

  def xg( x): 
    return tech.pitchPoly*tech.halfXGRGrid*2*x
  def yg( y): 
    return tech.pitchDG  *tech.halfYGRGrid*2*y

  def mirrorAcrossYAxis( adt):
    return ADITransform.mirrorAcrossYAxis().preMult( ADITransform.translate( adt.bbox.urx, 0))    


  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(10), yg(10)))

  adnetl =  ADNetlist( args.block_name)
  
  adnetl.addInstance( ADI( ndev, "un0", ADITransform.translate( xg(1), yg(1))))
  adnetl.addInstance( ADI( pdev, "up0", mirrorAcrossYAxis( pdev).preMult( ADITransform.translate( xg(8), yg(8)))))

  adnetl.connect('un0','g','i')
  adnetl.connect('un0','d','o')
  adnetl.connect('un0','s','vss')

  adnetl.connect('up0','g','i')
  adnetl.connect('up0','d','o')
  adnetl.connect('up0','s','vcc')

  adnetl.genNetlist( netl)

  netl.newGR( 'i', Rect( 1, 8, 8, 8), "metal4", tech.halfWidthM4[0]*2)
  netl.newGR( 'i', Rect( 1, 1, 1, 8), "metal3", tech.halfWidthM3[0]*2)

  netl.newGR( 'o', Rect( 8, 1, 8, 8), "metal3", tech.halfWidthM3[0]*2)
  netl.newGR( 'o', Rect( 1, 1, 8, 1), "metal4", tech.halfWidthM4[0]*2)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
