from collections import OrderedDict

from .converters import convert_align_to_adr
from ..cell_fabric.transformation import Rect, Transformation
from .base import Wire, Netlist

class ADT:
  def __init__( self, nm, *, physical_bbox=None):
    self.nm = nm
    assert physical_bbox is not None

    self.bbox = Rect( *physical_bbox)
    self.terminals = []

  def newWire( self, netName, rect, layer):
    w = Wire()
    w.netName = netName
    w.rect = rect
    w.layer = layer
    w.gid = -1
    self.terminals.append( w)
    return w

  def __repr__( self):
    return self.nm + "," + str(self.bbox) + "," + str(self.terminals)

class ADI:
  def __init__( self, t, iName, trans=None):
    self.template = t
    self.instanceName = iName
    self.formalActualMap = OrderedDict()
    self.trans = Transformation() if trans is None else trans

  def __repr__( self):
    return "template: %s instance: %s trans: %s" % (self.template, self.instanceName, self.trans)

  @property
  def bbox( self):
    return self.trans.hitRect( self.template.bbox).canonical()

class ADNetlist:
  @staticmethod
  def fromPlacerResults( nm, layer_map, placer_results):
    adnetl =  ADNetlist( nm)

    adts = {}

    for leaf in placer_results['leaves']:
      nm = leaf['template_name']
      adt = ADT( nm, physical_bbox=leaf['bbox'])
      adts[nm] = adt

      for term in leaf['terminals']:
        if term['layer'] in layer_map:
          # SY: Do not exclude !kor nets to propagate blockages thru hierarchy
          term = convert_align_to_adr(term)
          adt.newWire( term['net_name'], Rect( *term['rect']), term['layer'])

    for inst in placer_results['instances']:
      tN = inst['template_name']
      iN = inst['instance_name']
      tr = inst['transformation']

      adnetl.addInstance( ADI( adts[tN], iN, Transformation( **tr)))

      for (f,a) in inst['formal_actual_map'].items():
        adnetl.connect( iN, f, a)

    assert 'ports' not in placer_results

    if 'preroutes' in placer_results:
      for preroute in placer_results['preroutes']:
        adnetl.addPreroute(convert_align_to_adr(preroute))

    return adnetl.genNetlist( Rect( *placer_results['bbox']))


  def __init__( self, nm):
    self.nm = nm
    self.instances = OrderedDict()
    self.nets = OrderedDict()
    self.preroutes = []

  def addInstance( self, i):
    self.instances[i.instanceName] = i

  def addPreroute( self, p):
    self.preroutes.append( p)

  def connect( self, instanceName, f, a):
    if a not in self.nets:
      self.nets[a] = []
    self.nets[a].append( (instanceName,f))
    self.instances[instanceName].formalActualMap[f] = a

  def genNetlist( self, bbox): 
    netl = Netlist( nm=self.nm, bbox=bbox)

    self.ces = OrderedDict()
    self.kors = []
    for (_,v) in self.instances.items():

      netl.instances[v.instanceName] = v.bbox

      for w in v.template.terminals:
        fN = w.netName
        if fN in v.formalActualMap:
          aN = v.formalActualMap[fN]
          if aN not in self.ces: self.ces[aN] = {}
          pN = (v.instanceName, w.netName)
          if pN not in self.ces[aN]: self.ces[aN][pN] = []
          self.ces[aN][pN].append( (v.trans.hitRect( w.rect).canonical(), w.layer))
        else:
          self.kors.append( (v.trans.hitRect(w.rect).canonical(), w.layer))

    internally_connected = True
    for (aN,v) in self.ces.items():
      for ((iN,fN),vv) in v.items():
        for (r,l) in vv:
          if internally_connected:
            netl.newWire( aN, r, l, ceName=(iN,fN))
          else:
            netl.newWire( aN, r, l)

    for (r,l) in self.kors:
      assert l.startswith('metal') or l.startswith('via'), l
      netl.newWire( '!kor', r, l)
      
    for p in self.preroutes:
      netl.newWire( p['net_name'], Rect( *p['rect']), p['layer'])

    return netl

