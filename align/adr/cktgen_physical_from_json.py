from .cktgen import *

#
# Need to rename these or the router crashes with an stoi error?
#
from ..cell_fabric.transformation import Rect as tRect
from ..cell_fabric.transformation import Transformation

import json
from collections import defaultdict
import re


def extend( u, rng):
  if rng[0] is None or u < rng[0]: rng[0] = u
  if rng[1] is None or u > rng[1]: rng[1] = u
    

def trivial_gr( actual, v):

  x_rng = [ None,None]
  y_rng = [ None,None]

  for x in v:
    pin = (x[0],x[1])
    lst = x[2]

    for r in lst:
      extend( r[0], x_rng)
      extend( r[2], x_rng)
      extend( r[1], y_rng)
      extend( r[3], y_rng)

      

  last_count = 0
  tag = '+'
  for xc in range( x_rng[0], x_rng[1]+1):
    count = len( list(r for x in v for r in x[2] if r[0] <= xc <= r[2]))
    print( actual, xc, last_count, count, tag)

    if tag == '+' and last_count <= count: # still non-decreasing
      pass
    elif tag == '+' and last_count > count: # now decreasing
      print( "event")
      tag = '-'
    elif tag == '-' and last_count >= count: # still non-increasing
      pass
    elif tag == '-' and last_count < count: # now increasing 
      tag = '+'

    last_count = count

  if tag == '+':
    print("event")


  wires = []
  if False:

    xc0 = (2*x_rng[0]+x_rng[1])//3
    xc1 = (x_rng[0]+2*x_rng[1])//3

    if y_rng[1] > y_rng[0]:
      if xc1 > xc0:
        wires = [ {"layer": "metal3", "net_name": actual, "width": 320, "rect": [xc0, y_rng[0], xc0, y_rng[1]]},
                  {"layer": "metal3", "net_name": actual, "width": 320, "rect": [xc1, y_rng[0], xc1, y_rng[1]]}]
      else:
        wires = [ {"layer": "metal3", "net_name": actual, "width": 320, "rect": [xc0, y_rng[0], xc0, y_rng[1]]}]

    print( actual, pin, lst, x_rng, y_rng, wires)

  return wires



def main(args, tech):
  if args.consume_results: return
  
  assert args.source != ''
  src = args.source

  assert args.placer_json != ''

  with open( args.placer_json, "rt") as fp:
    placer_results = json.load( fp)

  if args.gr_json != '':
    gr_fn = args.gr_json
  else:
    gr_fn = f"INPUT/{src}_global_router_out.json"

  with open( gr_fn, "rt") as fp:
    global_router_results = json.load( fp)

  #
  # Need to get this from layers.json
  #
  metal_layer_map = { f'M{i}' : f'metal{i}' for i in range(0,7) }
  via_layer_map = { f'V{i}' : f'via{i}' for i in range(0,6) }
  layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))
  print("Layer map:", layer_map)

  adts = {}

  for leaf in placer_results['leaves']:
    nm = leaf['template_name']
    adt = ADT( tech, nm, physical_bbox=leaf['bbox'])
    adts[nm] = adt

    for term in leaf['terminals']:
      if term['layer'] in layer_map:
        # SY: Do not exclude !kor nets to propagate blockages thru hierarchy
        term = convert_align_to_adr(term)
        adt.newWire( term['net_name'], Rect( *term['rect']), term['layer'])

  bbox = placer_results['bbox']


  adnetl =  ADNetlist( args.block_name)

  for inst in placer_results['instances']:
    tN = inst['template_name']
    iN = inst['instance_name']
    tr = inst['transformation']

    # print( tr)

    adnetl.addInstance( ADI( adts[tN], iN, ADITransform( tr['oX'], tr['oY'], tr['sX'], tr['sY'])))

    for (f,a) in inst['formal_actual_map'].items():
      adnetl.connect( iN, f, a)

  if 'ports' in placer_results:  
    ports = placer_results['ports']
    for p in ports:
      adnetl.addPort( p)

  if 'preroutes' in placer_results:
    preroutes = placer_results['preroutes']
    for preroute in preroutes:
      adnetl.addPreroute(convert_align_to_adr(preroute))

  netl = Netlist( nm=args.block_name, bbox=Rect( *bbox))
  adnetl.genNetlist( netl)

  for wire in global_router_results['wires']:
    wire = convert_align_to_adr(wire)
    connected_pins = wire.get('connected_pins',None)
    # Enforce the new format
    assert connected_pins is not None

    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'], connected_pins=connected_pins)

    # netl.semantic()

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
