
import argparse
import pathlib
import math
from collections import OrderedDict

import json
import re

from . import techfile

class ADT:
  def __init__( self, tech, nm, *, physical_bbox=None):
    self.tech = tech
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

class ADITransform:
  def __init__( self, oX=0, oY=0, sX=1, sY=1):
    self.xOffset = oX
    self.yOffset = oY
    self.xScale = sX
    self.yScale = sY

  def __repr__( self):
    return "xo yo xs ys: %d %d %d %d" % ( self.xOffset, self.yOffset, self.xScale, self.yScale)

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
    self.preroutes = []

  def addInstance( self, i):
    self.instances[i.instanceName] = i

  def addPort( self, p):
    self.ports.append( p)

  def addPreroute( self, p):
    self.preroutes.append( p)

  def connect( self, instanceName, f, a):
    if a not in self.nets:
      self.nets[a] = []
    self.nets[a].append( (instanceName,f))
    self.instances[instanceName].formalActualMap[f] = a

  def genNetlist( self, netl): 
    self.ces = OrderedDict()
    self.kors = []
    for (_,v) in self.instances.items():
      for w in v.template.terminals:
        fN = w.netName
        if fN in v.formalActualMap:
          aN = v.formalActualMap[fN]
          if aN not in self.ces: self.ces[aN] = {}
          pN = (v.instanceName, w.netName)
          if pN not in self.ces[aN]: self.ces[aN][pN] = []
          self.ces[aN][pN].append( (v.hit( w.rect), w.layer))
        else:
          self.kors.append( (v.hit(w.rect), w.layer))

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
      
    # ports no longer used
    assert self.ports == []

    for p in self.preroutes:
      netl.newWire( p['net_name'], Rect( *p['rect']), p['layer'])

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

  def add_xxx( self, x, y):
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
    self.color = None

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
    self.connected_pins = None

  def __repr__(self):
    return f"{self.netName} {self.rect} {self.layer} {self.width}"

def encode_GR( tech, obj):
  if isinstance(obj, GR):
    # Convert global route coords to physical coords
    if obj.rect.llx == obj.rect.urx and obj.rect.lly == obj.rect.ury:
      raise RuntimeError( f"{obj} is a point.")
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
      raise RuntimeError( f"{obj} is not a horizontal or vertical line.")

    return { "netName" : obj.netName, "layer" : obj.layer, "width" : obj.width, "rect" : [llx, lly, urx, ury]}
  elif isinstance(obj, Wire):
    return { "netName" : obj.netName, "layer" : obj.layer, "gid" : obj.gid, "rect" : [obj.rect.llx, obj.rect.lly, obj.rect.urx, obj.rect.ury], "color": obj.color}
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

# SY: Added for coloring
def extract_layer_color(layer):
  """ Returns layer and color from colored layer. Example: viaa1 => via1, a"""
  mg = re.match(r'(metal|via)(\D+)(\d+)', layer)
  if mg:
    lyr = mg.group(1) + mg.group(3)
    clr = mg.group(2)
  else:
    lyr = layer
    clr = None
  return lyr, clr

# # SY: Added for coloring
# def extract_colored_layer(term):
#   """ Returns colored layer from a terminal. Example: {'layer': 'V1', 'color:'a'} => viaa1"""
#   if 'color' in term and term['color'] is not None:
#     mg = re.match(r'(metal|via)(\d+)', term['layer'])
#     assert mg, "Layer pattern not recognized"
#     layer = mg.group(1) + term['color'] + mg.group(2)
#   else:
#     layer = term['layer']
#   return layer

# SY: Added for coloring
def translate_layer(layer):
  """ Translates metal/via to M/V"""
  metal_layer_map = { f'metal{i}' : f'M{i}' for i in range(0,7) }
  via_layer_map = { f'via{i}' : f'V{i}' for i in range(0,6) }
  layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))
  return layer_map.get(layer, layer)

# SY: Syntax converter
def convert_align_to_adr(term):
    """ Convert align terminal to adr terminal (M -> colored metal, V -> colored via, netName -> net_name"""
    assert 'netName' in term, term
    new_term = dict()
    new_term['net_name'] = term['netName']
    new_term['rect'] = term['rect'].copy()
    prefix = 'metal' if term['layer'][0] == 'M' else 'via'
    if 'color' in term and term['color'] is not None:
        color = term['color']
    else:
        color = ''
    new_term['layer'] = prefix + color + term['layer'][1:]
    if 'width' in term:
        new_term['width'] = term['width']
    if 'connected_pins' in term:
        new_term['connected_pins'] = term['connected_pins'].copy()
    return new_term


class Net:
  def __init__( self, nm):
    self.nm = nm
    self.wires = []
    self.grs = []
    self.ces = OrderedDict()

class Netlist:
  def __init__( self, nm, bbox):
    self.nm = nm
    self.bbox = bbox
    self.nets = OrderedDict()
    self.gidIndex = 0
    self.instances = OrderedDict()
    self.wire_cache = {}

  def dumpGR( self, tech, fn, cell_instances=None, no_grid=False):
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

      if cell_instances is not None:
        for ci in cell_instances:
          terminals.append( ci)

      for (_,net) in self.nets.items():
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

      for term in terminals:
        # print('term::', type(term), term)
        if type(term) is dict:
          lyr, clr = extract_layer_color(term['layer'])
          term['layer'] = translate_layer(lyr)
          term['color'] = clr
        else:
          lyr, clr = extract_layer_color(term.layer)
          term.layer = translate_layer(lyr)
          term.color = clr

      data = { "bbox" : [self.bbox.llx, self.bbox.lly, self.bbox.urx, self.bbox.ury], "globalRoutes" : grs, "globalRouteGrid" : grGrid, "terminals" : terminals}


      fp.write( json.dumps( data, indent=2, default=lambda x: encode_GR(tech,x)) + "\n")

  def newWire( self, netName, r, l, *, ceName=None):
    """The wire cache is used to make sure we don't generate gid's for two different occs of the same wire """
    cand = (netName, (r.llx, r.lly, r.urx, r.ury), l)
    if cand not in self.wire_cache:
      w = Wire()
      w.netName = netName
      w.rect = r
      w.layer = l
      w.gid = self.gidIndex
      self.gidIndex += 1

      if netName not in self.nets:
        self.nets[netName] = Net( netName)

      self.nets[netName].wires.append( w)
      self.wire_cache[cand] = w
    else:
      w = self.wire_cache[cand]
      
    if ceName is not None:
      if ceName not in self.nets[netName].ces:
        self.nets[netName].ces[ceName] = []

      self.nets[netName].ces[ceName].append( w)

    return w

  def newGR( self, netName, r, l, w, *, connected_pins=None):
    gr = GR()

    gr.netName = netName
    gr.layer = l
    gr.rect = r.canonical()
    gr.width = w
    gr.connected_pins = connected_pins

    if netName not in self.nets:
      self.nets[netName] = Net( netName)

    self.nets[netName].grs.append( gr)

    return gr

  def write_ctrl_file( self, fn, route, show_global_routes, show_metal_templates, *, nets_to_route=None, nets_not_to_route=None, topmetal=''):
    if nets_to_route is not None:
      routes_str = f"Option name=nets_to_route value={','.join(nets_to_route)}"
    else:
      if nets_not_to_route is None:
        nets_not_to_route = []
      routes_str = f"Option name=nets_not_to_route value={','.join(nets_not_to_route + ['!kor'])}"

    if topmetal == '':
      topmetal = 'metal6'

    with open( fn, "w") as fp:
      fp.write( f"""# circuit-independent technology collateral
Option name=layer_file          value=DR_COLLATERAL/layers.txt
Option name=arch_file           value=DR_COLLATERAL/arch.txt
Option name=generator_file      value=DR_COLLATERAL/via_generators.txt
Option name=pattern_file        value=DR_COLLATERAL/patterns.txt
Option name=option_file         value=DR_COLLATERAL/design_rules.txt

# technology collateral may vary for different circuits
Option name=metal_template_file value=INPUT/{self.nm}_dr_metal_templates.txt

# circuit-specific collateral
Option name=global_routing_file value=INPUT/{self.nm}_dr_globalrouting.txt
Option name=input_file          value=INPUT/{self.nm}_dr_netlist.txt
Option name=option_file         value=INPUT/{self.nm}_dr_mti.txt
Option name=gr_merge_global_routes  value=0

# primary synthesis options
Option name=route       value={1 if route else 0}
Option name=solver_type value=glucose
Option name=allow_opens value=1

# custom routing options
{routes_str}

#Option name=opt_maximize_ties_between_trunks_and_terminals value=0
#Option name=opt_minimize_preroute_extensions value=0
#Option name=disable_optimization value=1

# debug options
Option name=create_fake_global_routes            value={1 if show_global_routes else 0}
Option name=create_fake_connected_entities       value=0
Option name=create_fake_ties                     value=0
Option name=create_fake_metal_template_instances value={1 if show_metal_templates else 0}
Option name=create_fake_line_end_grids           value=1
Option name=auto_fix_global_routing              value=0
Option name=pin_checker_mode                     value=0
Option name=upper_layer                          value={topmetal}

#Option name=disable_optimization value=1
# #OPT4 
# Option name=opt_maximize_ties_between_trunks value=0
# #OPT5
# Option name=opt_maximize_ties_between_trunks_and_terminals value=0
# Option name=opt_minimize_trunk_tracks value=0
# Option name=opt_optimize_trunk_positions value=0
# #OPT 6
# Option name=opt_minimize_preroute_extensions value=0
# #OPT 7
# Option name=opt_minimize_wire_tracks_soft value=0
# #OPT 8
# Option name=opt_minimize_ties_between_terminals value=0
# #OPT 9
# Option name=opt_maximize_routes_between_trunks_and_terminals value=0
# #OPT 10
# Option name=opt_minimize_wire_tracks_heavy value=0
# #OPT 11
# Option name=opt_maximize_routes_between_terminals value=0
# #OPT 12
# Option name=opt_maximize_routes_between_trunks value=0
# #OPT 13
# Option name=opt_optimize_width_of_trunks value=0
# #OPT 14
# Option name=opt_optimize_width_of_shunt_wires value=0
# #OPT 15
# Option name=opt_optimize_connections_to_terminals value=0
# #OPT 16
# Option name=opt_optimize_length_of_shunt_wires value=0
""")


  def write_input_file( self, fn):
    with open( fn, "w") as fp:
      fp.write( "Cell name=%s bbox=%s\n" % (self.nm, self.bbox))
      for (_,v) in self.nets.items():
        for w in v.wires:
          fp.write( str(w) + "\n")

  def write_global_routing_file( self, tech, fn):
    global_gr_id = 0

    with open( fn, "w") as fp:
      for (k,v) in self.nets.items():
        print("write_global_routing_file:Net:", k)
        fp.write( "#start of regular net %s\n" % k)

        if v.ces.values() is not []:
          ces = [ [ w.gid for w in vv] for vv in v.ces.values()]
        else:
          ces = [[w.gid] for w in v.wires]


        pin_ids = set()

        for gr in v.grs:
          if gr.connected_pins is not None:
            print(gr.rect,gr.connected_pins)


            for cp in gr.connected_pins:
              assert cp['layer'] == 'M2'
              # convert to Angstroms (probably should do this elsewhere)
              rect = [ v*5 for v in cp['rect']]

              cand = ( gr.netName, tuple(rect), "metal2")

              x0 = rect[0]/(840*10)
              x2 = rect[2]/(840*10)

              pin_gr_pitches_long = abs(x2 - x0)
              if pin_gr_pitches_long > 0.5 and gr.layer in ["metal2","metal4"]:
                print( f"Long ({round(pin_gr_pitches_long,2)} pitches) horizonal pin found", cand, gr)

                min_x = None, None
                for x_gr in range(gr.rect.llx,gr.rect.urx+1):
                  for x_pin in range(int(x0),int(x2)+1):
                    cand2 = abs(x_gr-x_pin)
                    #pylint: disable=used-before-assignment
                    if min_x[0] is None or cand2 < best:
                      min_x = x_gr,x_pin
                      best = cand2
                print( "best", cand, min_x, best, gr.rect, x0, x2)


              hier_name = cp['sink_name'].split('/')

              if cand in self.wire_cache:
                print( 'connected pin found for:', k, hier_name, cand)
                wire = self.wire_cache[cand]
                pin_ids.add( wire.gid)
              elif len(hier_name)>1:
                print( 'connected pin not found for:', k, hier_name, cand)
                assert hier_name[0] in ["C1","C2","R1","R2"]
              else:
                 print( 'connected top-level pin not found for:', k, hier_name, cand)


        if False:
          for lst in ces:
            if pin_ids:
              nlst = [ gid for gid in lst if gid in pin_ids]
            else:
              nlst = lst

            if not nlst:
              nlst = lst

            fp.write( "ConnectedEntity terms=%s\n" % (','.join( [ str(gid) for gid in nlst])))
        else:
          # connect everything (no via preroutes)
          skip_via_set = set(["via0","via1","via2","via3","via4"])
          for w in v.wires:
            ly = w.layer
            if ly in skip_via_set: continue
            fp.write( "ConnectedEntity terms=%s\n" % w.gid)

        grs = []
        for gr in v.grs:
          if gr.rect.llx == gr.rect.urx and gr.rect.lly == gr.rect.ury: continue
          gr.gid = global_gr_id
          grs.append( "(%d,%d,%d,%d,%s,gid=%d,minw=%d)" % (gr.rect.llx,
                                                           gr.rect.lly,
                                                           gr.rect.urx,
                                                           gr.rect.ury,
                                                           gr.layer,
                                                           gr.gid,
                                                           gr.width))
          global_gr_id += 1

        fp.write( "GlobalRouting net=%s routes=%s\n" % (k,';'.join(grs)))

        if False:
          for gr in v.grs:
            if not hasattr(gr,'gid'): continue
            if gr.rect.llx == gr.rect.urx and gr.rect.lly == gr.rect.ury: continue
            if gr.connected_pins is not None:
              for cp in gr.connected_pins:
                assert cp['layer'] == 'M2'
                rect = [ v*5 for v in cp['rect']]
                cand = ( gr.netName, tuple(rect), "metal2")
                if cand in self.wire_cache:
                  wire = self.wire_cache[cand]
                  fp.write( "Tie term0=%d gr0=%d\n" % (wire.gid, gr.gid))
        elif True:
          dx = tech.pitchPoly*tech.halfXGRGrid*2
          dy = tech.pitchDG  *tech.halfYGRGrid*2
          def touching( r0, r1):
            # (not touching) r0.lly > r1.ury or r1.lly > r0.ury
            check1 = r0.lly <= r1.ury and r1.lly <= r0.ury
            check2 = r0.llx <= r1.urx and r1.llx <= r0.urx
            return check1 and check2

          for gr in v.grs:
            x0 =   (gr.rect.llx)*dx + self.bbox.llx
            x1 = (1+gr.rect.urx)*dx + self.bbox.llx
            y0 =   (gr.rect.lly)*dy + self.bbox.lly
            y1 = (1+gr.rect.ury)*dy + self.bbox.lly
            gr_r = Rect( x0, y0, x1, y1)
            print( "Metal GR:", gr, gr_r)

            tuples = [
              ("metal1", ["metal1","metal0"]),
              ("metal2", ["metal3","metal2","metal1"]),
              ("metal3", ["metal4","metal3","metal2"]),
              ("metal4", ["metal5","metal4","metal3"]),
              ("metal5", ["metal6","metal5","metal4"]),
              ("metal6", ["metal7","metal6","metal5"])
              ]

            for gr_layer, w_layers in tuples:
              if gr.layer == gr_layer:
                for w in v.wires:
                  if extract_layer_color(w.layer)[0] in w_layers:
                    if touching( gr_r, w.rect):
                      fp.write( "Tie term0=%d gr0=%d\n" % (w.gid, gr.gid))
                      print( "Tie", gr, gr_r, w)

        fp.write( "#end of net %s\n" % k)


  def write_files( self, tech, dirname, args):

    if args.nets_to_route == '':
      nets_to_route = None
    else:
      nets_to_route = args.nets_to_route.split(',')

    if args.nets_not_to_route == '':
      nets_not_to_route = None
    else:
      nets_not_to_route = args.nets_not_to_route.split(',')

    self.write_ctrl_file( dirname + "/ctrl.txt", args.route, args.show_global_routes, args.show_metal_templates, nets_to_route=nets_to_route, nets_not_to_route=nets_not_to_route, topmetal=args.topmetal)


    self.write_input_file( dirname + "/" + self.nm + "_dr_netlist.txt")
    self.write_global_routing_file( tech, dirname + "/" + self.nm + "_dr_globalrouting.txt")
    self.dumpGR( tech, dirname + "/" + self.nm + "_dr_globalrouting.json", no_grid=True)


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
        continue

      m = p_obj_lbrace.match( line)
      if m:
        net = m.groups()[0]
        continue

      m = p_wire_in_obj.match( line)
      if m:
        net = m.groups()[0]
        layer = m.groups()[1]
        rect = Rect( int(m.groups()[2]), int(m.groups()[3]), int(m.groups()[4]), int(m.groups()[5]))

        if True or layer in ["via0","via1","via2","via3","via4"]:
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

from .consume_results import consume_results

def parse_args( command_line_args=None):
  parser = argparse.ArgumentParser( description="Generates input files for amsr (Analog router)")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "--route", action='store_true')
  parser.add_argument( "--show_global_routes", action='store_true')
  parser.add_argument( "--show_metal_templates", action='store_true')
  parser.add_argument( "--consume_results", action='store_true')
  parser.add_argument( "--no_interface", action='store_true')
  parser.add_argument( "--placer_json", type=str, default='')
  parser.add_argument( "--gr_json", type=str, default='')
  parser.add_argument( "-tf", "--technology_file", type=str, default="DR_COLLATERAL/Process.json")
  parser.add_argument( "-s", "--source", type=str, default='')
  parser.add_argument( "--small", action='store_true')
  parser.add_argument( "--nets_to_route", type=str, default='')
  parser.add_argument( "--nets_not_to_route", type=str, default='')
  parser.add_argument( "-tm", "--topmetal", type=str, default='')

  args = parser.parse_args( args=command_line_args)

  with open( args.technology_file) as fp:
    tech = techfile.TechFile( fp)

  if args.consume_results:
    consume_results(args,tech)
    # exit()

  return args,tech
