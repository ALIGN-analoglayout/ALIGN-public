
import argparse
import pathlib
from collections import OrderedDict

import json

from . import techfile

class ADT:
  def __init__( self, tech, nm, npp=10, nr=1, *, physical_bbox=None):
    self.tech = tech
    self.nm = nm
    if physical_bbox is None:
      self.bbox = Rect( 0, 0, npp*self.tech.pitchPoly, nr*self.tech.dgPerRow*self.tech.pitchDG)
    else:
      self.bbox = Rect( *physical_bbox)

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

  def addM1Terminal( self, netName, m1TracksOffset=None, rect=None, leaf_bbox=None):
    """Add a m1 terminal (vertical) that spans the entire ADT and is centered on track m1TracksOffset (zero is the left boundary of the cell) or corresponds to rect
"""
    assert m1TracksOffset is None or rect is None
    assert m1TracksOffset is not None or rect is not None

    if m1TracksOffset is not None:
      xc = self.tech.pitchM1*m1TracksOffset

      y0 = self.bbox.lly+self.tech.halfMinETESpaceM1
      y1 = self.bbox.ury-self.tech.halfMinETESpaceM1

    if rect is not None:
      assert rect[0] == rect[2]
      assert leaf_bbox is not None

      xc = self.tech.pitchM1*rect[0]

      # HACK: This is different than the other odd layers
      # We are using the "placer" level abstraction --- Needs to eventually change
      height_fraction = (self.bbox.ury-self.bbox.lly) // leaf_bbox[3]
      y0 = height_fraction*rect[1]+self.tech.halfMinETESpaceM1
      y1 = height_fraction*rect[3]-self.tech.halfMinETESpaceM1

    x0 = xc-self.tech.halfWidthM1[0]
    x1 = xc+self.tech.halfWidthM1[0]

    return self.newWire( netName, Rect( x0, y0, x1, y1), "metal1")

  def addM2Terminal( self, netName, rect):
    """Add a m2 terminal (horizontal) that corresponds to rect
"""

    assert rect[1] == rect[3]

    yc = self.tech.pitchM3*rect[1]

    # HACK: need to use the correct stopping point grid (assuming M2 and M3 pitches are the same.)
    # expand from abstract grid
    x0 = self.tech.pitchM3*rect[0]-self.tech.halfMinETESpaceM2
    x1 = self.tech.pitchM3*rect[2]+self.tech.halfMinETESpaceM2

    y0 = yc-self.tech.halfWidthM2[0]
    y1 = yc+self.tech.halfWidthM2[0]

    return self.newWire( netName, Rect( x0, y0, x1, y1), "metal2")

  def addM3Terminal( self, netName, m3TracksOffset=None, rect=None):
    """Add a m3 terminal (vertical) that spans the entire ADT and is centered on track m1TracksOffset (zero is the left boundary of the cell) or corresponds to rect
"""
    assert m3TracksOffset is None or rect is None
    assert m3TracksOffset is not None or rect is not None

    if m3TracksOffset is not None:
      xc = self.tech.pitchM3*m3TracksOffset

      y0 = self.bbox.lly+self.tech.halfMinETESpaceM3
      y1 = self.bbox.ury-self.tech.halfMinETESpaceM3

    if rect is not None:
      assert rect[0] == rect[2]

      xc = self.tech.pitchM3*rect[0]

      # HACK: need to use the correct stopping point grid (assuming M2 and M3 pitches are the same.)
      # expand from abstract grid
      y0 = self.tech.pitchM3*rect[1]-self.tech.halfMinETESpaceM3
      y1 = self.tech.pitchM3*rect[3]+self.tech.halfMinETESpaceM3

    x0 = xc-self.tech.halfWidthM3[0]
    x1 = xc+self.tech.halfWidthM3[0]

    return self.newWire( netName, Rect( x0, y0, x1, y1), "metal3")

  def addM4Terminal( self, netName, rect):
    """Add a m4 terminal (horizontal) that corresponds to rect
"""

    assert rect[1] == rect[3]

    yc = self.tech.pitchM3*rect[1]

    # HACK: need to use the correct stopping point grid (assuming M4 and M5 pitches are the same.)
    # expand from abstract grid
    x0 = self.tech.pitchM5*rect[0]-self.tech.halfMinETESpaceM4
    x1 = self.tech.pitchM5*rect[2]+self.tech.halfMinETESpaceM4

    y0 = yc-self.tech.halfWidthM4[0]
    y1 = yc+self.tech.halfWidthM4[0]

    return self.newWire( netName, Rect( x0, y0, x1, y1), "metal4")

  def addM5Terminal( self, netName, m5TracksOffset=None, rect=None):
    """Add a m5 terminal (vertical) that spans the entire ADT and is centered on track m1TracksOffset (zero is the left boundary of the cell) or corresponds to rect
"""
    assert m5TracksOffset is None or rect is None
    assert m5TracksOffset is not None or rect is not None

    if m5TracksOffset is not None:
      xc = self.tech.pitchM5*m5TracksOffset

      y0 = self.bbox.lly+self.tech.halfMinETESpaceM5
      y1 = self.bbox.ury-self.tech.halfMinETESpaceM5

    if rect is not None:
      assert rect[0] == rect[2]

      xc = self.tech.pitchM5*rect[0]

      # HACK: need to use the correct stopping point grid (assuming M4 and M5 pitches are the same.)
      # expand from abstract grid
      y0 = self.tech.pitchM5*rect[1]-self.tech.halfMinETESpaceM5
      y1 = self.tech.pitchM5*rect[3]+self.tech.halfMinETESpaceM5

    x0 = xc-self.tech.halfWidthM5[0]
    x1 = xc+self.tech.halfWidthM5[0]

    return self.newWire( netName, Rect( x0, y0, x1, y1), "metal5")

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
    self.ports = []

  def addInstance( self, i):
    self.instances[i.instanceName] = i

  def addPort( self, p):
    self.ports.append( p)

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
        if w.netName not in v.formalActualMap:
          print( "Converting disconnected net to !kor", w.netName)

        a = "!kor" if w.netName not in v.formalActualMap else v.formalActualMap[w.netName]
        if True or a not in ["vcc","vss"]:
          netl.newWire( a, v.hit( w.rect), w.layer)
#          print( "genNetlist", w, v.hit( w.rect))

    for p in self.ports:
      print( "Port", p)
      r = p['rect']
      ly = p['layer']
      if ly in ["metal1","metal3","metal5"]:
        netl.newWire( p['net_name'], Rect( r[0]*720-200, r[1]*720-360, r[2]*720+200, r[3]*720+360), ly)
      if ly in ["metal2","metal4","metal6"]:
        netl.newWire( p['net_name'], Rect( r[0]*720-360, r[1]*720-200, r[2]*720+360, r[3]*720+200), ly)

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

  def dumpGR( self, tech, fn, cell_instances=[], no_grid=False):
    with open( fn, "w") as fp:
# mimic what flatmap would do
      grs = []
      terminals = []

      print( cell_instances)

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

      for ci in cell_instances:
        terminals.append( ci)

      for (netName,net) in self.nets.items():
        for gr in net.grs:
          grs.append(gr)
        for wire in net.wires:
          terminals.append( wire)

      grGrid = []
      if not no_grid:
        dx = tech.pitchPoly*tech.halfXGRGrid*2
        dy = tech.pitchDG*tech.halfYGRGrid*2
        for x in range( self.bbox.llx, self.bbox.urx, dx):
          for y in range( self.bbox.lly, self.bbox.ury, dy):
            grGrid.append( [x,y,x+dx,y+dy])
      else:
        grGrid.append( self.bbox.toList())
            

      data = { "bbox" : [self.bbox.llx, self.bbox.lly, self.bbox.urx, self.bbox.ury], "globalRoutes" : grs, "globalRouteGrid" : grGrid, "terminals" : terminals}


      fp.write( json.dumps( data, indent=2, default=lambda x: encode_GR(tech,x)) + "\n")

      ys = set()
      ys2 = set()

      for term in data['terminals']:
        if isinstance( term, Wire):
          if term.layer == 'M2':
            r = term.rect
            yc = (r.lly+r.ury)//2
            ys.add(yc)
            ys2.add(yc%840)

      print(sorted(list(ys)))
      print(sorted(list(ys2)))



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
      fp.write( f"""# circuit-independent technology collateral
Option name=layer_file          value=DR_COLLATERAL/layers.txt
Option name=arch_file           value=DR_COLLATERAL/arch.txt
Option name=generator_file      value=DR_COLLATERAL/car_generators.txt
Option name=pattern_file        value=DR_COLLATERAL/v2_patterns.txt
Option name=option_file         value=DR_COLLATERAL/design_rules.txt

# technology collateral may vary for different circuits
Option name=metal_template_file value=INPUT/{self.nm}_dr_metal_templates.txt

# circuit-specific collateral
Option name=global_routing_file value=INPUT/{self.nm}_dr_globalrouting.txt
Option name=input_file          value=INPUT/{self.nm}_dr_netlist.txt
Option name=option_file         value=INPUT/{self.nm}_dr_mti.txt

# primary synthesis options
Option name=route       value={1 if route else 0}
Option name=solver_type value=glucose
Option name=allow_opens value=1

# custom routing options
#Option name=nets_to_route value=i,o
Option name=nets_not_to_route value=!kor,vss,vcc

# debug options
Option name=create_fake_global_routes            value={1 if show_global_routes else 0}
Option name=create_fake_connected_entities       value=0
Option name=create_fake_ties                     value=0
Option name=create_fake_metal_template_instances value={1 if show_metal_templates else 0}
Option name=create_fake_line_end_grids           value=1
""")


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
    self.dumpGR( tech, dir + "/" + self.nm + "_dr_globalrouting.json", no_grid=True)



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

        # hack to get rid of large global routing visualization grid
        if layer != "nwell":
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

        # hack to get rid of large global routing visualization grid
        if layer != "nwell":
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

        if True or layer in ["via1","via2","via3","via4"]:
          w = netl.newWire( net, rect, layer)
          w.gid = None

        continue

      m = p_rbrace.match( line)
      if m:

        continue

      m = p_space.match( line)
      if m: continue

      assert False, line

  return netl

from . import transformation

class Scanline:
    def __init__(self, proto, indices, dIndex):
        self.proto = proto
        self.indices = indices
        self.dIndex = dIndex
        self.rects = []
        self.clear()

    def clear(self):
        self.start = None
        self.end = None
        self.currentNet = None

    def isEmpty(self):
        return self.start is None

    def emit(self):
        r = self.proto[:]
        r[self.dIndex] = self.start
        r[self.dIndex+2] = self.end
        self.rects.append((r, self.currentNet))

    def set(self, rect, netName):
        self.start = rect[self.dIndex]
        self.end = rect[self.dIndex+2]
        self.currentNet = netName


def removeDuplicates( data):

    layers = [('metal0', 'h'), ('metal1', 'v'), ('metal2', 'h'),('metal3', 'v'),
              ('metal4', 'h'), ('metal5', 'v'), ('metal6', 'h'),('metal7', 'v')]

    viaLayers = {'via0','via1','via2','via3','via4','via5','via6'}

    hLayers = {layer for (layer, dir) in layers if dir == 'h'}
    vLayers = {layer for (layer, dir) in layers if dir == 'v'}
    layersDict = dict(layers)

    indicesTbl = {'h': ([1, 3], 0), 'v': ([0, 2], 1)}

    tbl = {}

    tblVia = {}

    for d in data:
        layer = d['layer']
        rect = d['rect']
        netName = d['net_name']

        if layer in viaLayers:
          twice_centers = ( rect[0]+rect[2], rect[1]+rect[3])
          if layer not in tblVia:
            tblVia[layer] = {}
          if twice_centers not in tblVia[layer]:
            tblVia[layer][twice_centers] = []
          tblVia[layer][twice_centers].append((rect, netName))
        elif layer not in layersDict:
          if layer not in ["nwell"]:
            print( "Skipping processing of unknown layer:", layer)
        else:
          twice_center = sum(rect[index] for index in indicesTbl[layersDict[layer]][0])
          if layer not in tbl:
            tbl[layer] = {}
          if twice_center not in tbl[layer]:
            tbl[layer][twice_center] = []
          tbl[layer][twice_center].append((rect, netName))

    terminals = []

    for layer in viaLayers:
      if layer not in tblVia:
        continue

      for (k,v) in tblVia[layer].items():
        assert len(v) >= 0
        for p in v[1:]:
          if p[0] != v[0][0]:
            print( "Via rectangles with same center differ:", layer, k, v)
          if p[1] != v[0][1]:
            print( "Via nets with same center differ:", layer, k, v)

        # only the first one
        for p in v[:1]:
          terminals.append({'layer': layer, 'net_name': p[1], 'rect': p[0]})

    for (layer, dir) in layers:
        if layer not in tbl:
            continue
        (indices, dIndex) = indicesTbl[dir]

        for (twice_center, v) in tbl[layer].items():

            sl = Scanline(v[0][0], indices, dIndex)

            if v:
                (rect0, _) = v[0]
                for (rect, netName) in v[1:]:
                    assert all(rect[i] == rect0[i] for i in indices)

                s = sorted(v, key=lambda p: p[0][dIndex])

                for (rect, netName) in s:
                    if sl.isEmpty():
                        sl.set(rect, netName)
                    elif rect[dIndex] <= sl.end:  # continue
                        sl.end = max(sl.end, rect[dIndex+2])
                        if sl.currentNet != netName:
                            print( "Potential short:", (layer, sl.currentNet, netName))
                        #assert sl.currentNet == netName, (layer, sl.currentNet, netName)
                    else:  # gap
                        sl.emit()
                        sl.set(rect, netName)

                if not sl.isEmpty():
                    sl.emit()
                    sl.clear()


#        print( layer, twice_center, len(v), len(sl.rects))

            for (rect, netName) in sl.rects:
                terminals.append(
                    {'layer': layer, 'net_name': netName, 'rect': rect})

    return terminals


def consume_results(args,tech):
    with open( 'out/' + args.block_name + '.lgf', 'rt') as fp:  
      netl = parse_lgf( fp)

    placer_results = None  
    if args.placer_json != "":
      with open( args.placer_json, 'rt') as fp:  
        placer_results = json.load( fp)

        
    terminals = []
    if placer_results is not None:
      if args.no_interface:
        globalScale = transformation.Transformation( 0, 0, 1, 1)
      else:        
        globalScale = transformation.Transformation( 0, 0, tech.halfXADTGrid*tech.pitchPoly, tech.halfYADTGrid*tech.pitchDG)

      leaves_map = { leaf['template_name'] : leaf for leaf in placer_results['leaves']}

      for inst in placer_results['instances']:
        leaf = leaves_map[inst['template_name']]
        tr = inst['transformation']
        trans = transformation.Transformation( tr['oX'], tr['oY'], tr['sX'], tr['sY'])
        r = globalScale.hitRect( trans.hitRect( Rect( *leaf['bbox'])).canonical())

        nm = placer_results['nm'] + '/' + inst['instance_name'] + ':' + inst['template_name']
        terminals.append( { "netName" : nm, "layer" : "cellarea", "rect" : r.toList()})
      
    netl.write_input_file( netl.nm + "_xxx.txt")

    netl.dumpGR( tech, "INPUT/" + args.block_name + "_dr_globalrouting.json", cell_instances=terminals, no_grid=args.small)

    if args.no_interface:
      return

    leaf = {}

    design_name = netl.nm
    if args.source != "":
      design_name = args.source

    leaf['template_name'] = design_name

#
# A lot to do here. This should be moved to the technology file
#
#
# First assume there is only one metal template per layer
# And only one wire width and space
#
    layer2MetalTemplate = {}
    for obj in tech.metalTemplates:
      assert obj.layer not in layer2MetalTemplate
      layer2MetalTemplate[obj.layer] = obj

    def pgd_pitch(mt):
      assert len(mt.widths) == 2 and len(mt.spaces) == 1
      assert mt.widths[0] == mt.widths[1]
      return mt.widths[0] + mt.spaces[0]

    def pgd_width(mt):
      assert len(mt.widths) == 2 and len(mt.spaces) == 1
      assert mt.widths[0] == mt.widths[1]
      return mt.widths[0]

    def ogd_pitch(mt):
      assert len(mt.stops) == 1
      return mt.stops[0]

    def ogd_offset(mt):
      assert len(mt.stops) == 1
      return mt.stop_offset


#
# Use metal1 and metal2 for bbox grid
#
    shrinkX = pgd_pitch(layer2MetalTemplate['metal1'])
    shrinkY = pgd_pitch(layer2MetalTemplate['metal2'])
    
    bbox = netl.bbox
    assert bbox.llx == 0
    assert bbox.lly == 0
    assert bbox.urx % shrinkX == 0
    assert bbox.ury % shrinkY == 0

    leaf['bbox'] = [ bbox.llx // shrinkX, bbox.lly // shrinkY, bbox.urx // shrinkX, bbox.ury // shrinkY]

    leaf['terminals'] = []
    leaf['layout'] = []

    p = re.compile('^MTI_.*|^.*_gr$')

#
# Need to do this first since via enclosure don't necessary land on the stopping point grid
#
    layout = []
    for (_,wire) in netl.wires.items():
      if p.match(wire.netName): continue
      layout.append( {
        "net_name": wire.netName,
        "layer": wire.layer,
        "rect": wire.rect.toList()
      })
    layout = removeDuplicates(layout)

    for obj in layout:
      netName = obj['net_name']
      rect = Rect( *obj['rect'])
      layer = obj['layer']

      if p.match(netName): continue

      if layer in ["metal3","metal5","metal7"]:
        mt = layer2MetalTemplate[layer]
        halfWidth = pgd_width(mt) // 2
        pgdPitch = pgd_pitch(mt)
        ogdPitch = ogd_pitch(mt)
        ogdOffset = ogd_offset(mt)

        assert (rect.llx+halfWidth) % pgdPitch == 0
        assert rect.lly % ogdPitch == ogdOffset, (rect.lly, rect.lly % ogdPitch)
        assert (rect.urx-halfWidth) % pgdPitch == 0
        assert rect.ury % ogdPitch == ogdOffset, (rect.ury, rect.ury % ogdPitch)

        cx = (rect.urx + rect.llx) // (2*pgdPitch)
        # shrink to abstract grid
        y0 = (rect.lly + ogdOffset) // ogdPitch
        y1 = (rect.ury - ogdOffset) // ogdPitch

        leaf['terminals'].append({
          "net_name": netName,
          "layer": layer,
          "rect": [ cx, y0, cx, y1]
        })

      if layer in ["metal2","metal4","metal6"]:
        mt = layer2MetalTemplate[layer]
        halfWidth = pgd_width(mt) // 2
        pgdPitch = pgd_pitch(mt)
        ogdPitch = ogd_pitch(mt)
        ogdOffset = ogd_offset(mt)

        assert (rect.lly+halfWidth) % pgdPitch == 0
        assert rect.llx % ogdPitch == ogdOffset, (rect.llx, rect.llx % ogdPitch)
        assert (rect.ury-halfWidth) % pgdPitch == 0
        assert rect.urx % ogdPitch == ogdOffset, (rect.urx, rect.urx % ogdPitch)

        cy = (rect.ury + rect.lly) // (2*pgdPitch)
        # shrink to abstract grid
        x0 = (rect.llx + ogdOffset) // ogdPitch
        x1 = (rect.urx - ogdOffset) // ogdPitch

        leaf['terminals'].append({
          "net_name": netName,
          "layer": layer,
          "rect": [ x0, cy, x1, cy]
        })

    leaf['terminals'] = removeDuplicates(leaf['terminals'])
    leaf['layout'] = layout

    interface_fn = "INPUT/interface.json"
    if args.source != '':
      interface_fn = "INPUT/" + args.source + "_interface.json"

    with open( interface_fn, "wt") as fp:
      fp.write( json.dumps( { "leaves": [ leaf ]}, indent=2) + "\n")


def parse_args():
  parser = argparse.ArgumentParser( description="Generates input files for amsr (Analog router)")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "--route", action='store_true')
  parser.add_argument( "--show_global_routes", action='store_true')
  parser.add_argument( "--show_metal_templates", action='store_true')
  parser.add_argument( "--consume_results", action='store_true')
  parser.add_argument( "--no_interface", action='store_true')
  parser.add_argument( "--placer_json", type=str, default='')
  parser.add_argument( "-tf", "--technology_file", type=str, default="DR_COLLATERAL/Process.json")
  parser.add_argument( "-s", "--source", type=str, default='')
  parser.add_argument( "--small", action='store_true')

  args = parser.parse_args()

  with open( args.technology_file) as fp:
    tech = techfile.TechFile( fp)

  if args.consume_results:
    consume_results(args,tech)
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
