from .cktgen import *

#
# Need to rename these or the router crashes with an stoi error?
#
from .transformation import Rect as tRect
from .transformation import Transformation

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

def gr_hints(parser_results):
  leaf_map = { x['template_name'] : x for x in placer_results['leaves'] }

  net_map = defaultdict(list)
  for inst in placer_results['instances']:
    i = inst['instance_name']
    t = inst['template_name']
    assert t in leaf_map
    leaf = leaf_map[t]
    pin_map = defaultdict(list)
    for terminal in leaf['terminals']:
      pin_map[terminal['net_name']].append( terminal)

    tr = inst['transformation']
    trans = Transformation( tr['oX'], tr['oY'], tr['sX'], tr['sY'])

    for (formal,actual) in inst['formal_actual_map'].items():
      assert formal in pin_map
      lst = [trans.hitRect( tRect( *terminal['rect'])).canonical() for terminal in pin_map[formal]]

      gr_lst = [ [ int(t//(10*840)) for t in r.toList()] for r in lst]

      net_map[actual].append( (i,formal,gr_lst))

  wires = []
  for (k,v) in net_map.items():
    tmp = trivial_gr( k, v)
    wires += tmp

  return wires


def hack_gr( results, bbox):
  wires = results['wires']

  print("SMB")

  metal_layer_map = { f'M{i}' : f'metal{i}' for i in range(2,5) }
  via_layer_map = { f'V{i}' : f'via{i}' for i in range(1,4) }
  layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))

  print(layer_map)
  
# change metal2 grs to metal4 (big runtime issue otherwise)
#  layer_map['M2'] = 'metal4'

  horizontal_layers = ["metal2","metal4"]
  vertical_layers = ["metal1","metal3"]

  binsize = 84*2*10
  def gbin(v):
    return v//binsize

  assert bbox[2] % 5 == 0
  assert bbox[3] % 5 == 0

  bbox_urx = bbox[2]//5
  bbox_ury = bbox[3]//5
 
  print("bin of bbox_urx", gbin(bbox_urx))
  print("bin of bbox_ury", gbin(bbox_ury))

  def dnx(v):
    return max(gbin(bbox[0]),gbin(v))

  def dny(v):
    return max(gbin(bbox[1]),gbin(v))

  def upx(v):
    return min(gbin(bbox_urx)-1,gbin(v))

  def upy(v):
    return min(gbin(bbox_ury)-1,gbin(v))

  expand_null_routes = True

  new_wires = []
  for wire in wires:
    r = [ v+0 for v in Rect( *wire['rect']).canonical().toList() ]

    tuples = []
    for v in r:
      rem = v % binsize
      gcd = math.gcd(rem,binsize)
      tuples.append( (v//binsize, rem//gcd, binsize//gcd))

    print( "module grid", tuples[1], tuples[3])

    ly = layer_map[wire['layer']]

    nr = [ gbin(r[0]), gbin(r[1]), gbin(r[2]), gbin(r[3])]

    # Make sure everything is within bounds

    if ly in vertical_layers:
      if nr[2] >= gbin(bbox_urx)-1:
        nr[0] = nr[2] = gbin(bbox_urx)-1
      assert 0 <= nr[0] < gbin(bbox_urx), (nr, ly, gbin(bbox_urx))
      assert 0 <= nr[2] < gbin(bbox_urx), (nr, ly, gbin(bbox_urx))

      if nr[1] > gbin(bbox_ury)-1:
        nr[1] = gbin(bbox_ury)-1
      if nr[3] > gbin(bbox_ury)-1:
        nr[3] = gbin(bbox_ury)-1

    elif ly in horizontal_layers:
      if nr[3] >= gbin(bbox_ury)-1:
        nr[1] = nr[3] = gbin(bbox_ury)-1
      assert 0 <= nr[1] < gbin(bbox_ury), (nr, ly, gbin(bbox_urx))
      assert 0 <= nr[3] < gbin(bbox_ury), (nr, ly, gbin(bbox_urx))

      if nr[0] > gbin(bbox_urx)-1:
        nr[0] = gbin(bbox_urx)-1
      if nr[2] > gbin(bbox_urx)-1:
        nr[2] = gbin(bbox_urx)-1

    else:
      assert False, ly

    # Make sure we don't have 2d routes
    assert nr[0] == nr[2] or nr[1] == nr[3], (r,nr)

#    if expand_null_routes and (nr[0] == nr[2] and nr[1] == nr[3]):
    if expand_null_routes:
      if ly in vertical_layers:
        # extend the wire to be at least a grid long
        dy = r[3]-r[1]
        if dy < binsize:
          extend = (binsize-dy)//2
          nr = [ nr[0], dny(r[1]-extend), nr[2], upy(r[3]+extend)]

        if nr[1] == nr[3]:
          if nr[3] == 0:
            nr[3] += 1
          if nr[1] == gbin(bbox_ury)-1:
            nr[1] -= 1

        assert nr[1] != nr[3], (r,nr)

      elif ly in horizontal_layers:

        dx = r[2]-r[0]
        if dx < binsize:
          extend = (binsize-dx)//2
          nr = [ dnx(r[0]-extend), nr[1], upx(r[2]+extend), nr[3]]

        if nr[0] == nr[2]:
          if nr[2] == 0:
            nr[2] += 1
          if nr[0] == gbin(bbox_urx)-1:
            nr[0] -= 1

        assert nr[0] != nr[2], (r,nr)

      else:
        assert False, ly

    # Not a point
    assert nr[0] != nr[2] or nr[1] != nr[3], (r,nr)
    # Not 2D
    assert nr[0] == nr[2] or nr[1] == nr[3], (r,nr)
    # in range
    assert 0 <= nr[0] < gbin(bbox_urx), (nr, ly, gbin(bbox_urx))
    assert 0 <= nr[2] < gbin(bbox_urx), (nr, ly, gbin(bbox_urx))
    assert 0 <= nr[1] < gbin(bbox_ury), (nr, ly, gbin(bbox_urx))
    assert 0 <= nr[3] < gbin(bbox_ury), (nr, ly, gbin(bbox_urx))

    new_wire = { 'layer': ly,
                 'net_name': wire['net_name'],
                 'width': 320,
                 'rect': nr
    }
    if "connected_pins" in wire:
      new_wire['connected_pins'] = wire['connected_pins']

    if not expand_null_routes or nr[0] != nr[2] or nr[1] != nr[3]:
      new_wires.append(new_wire)
    else:
      assert not expand_null_routes
      print("Removing zero size global route", new_wire)

  results['wires'] = new_wires


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

  #  hack_gr( global_router_results, placer_results['bbox'])
  #  wires = gr_hints(placer_results)
  #  global_router_results = { "wires": wires}

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

  netl = Netlist( nm=args.block_name, bbox=Rect( *bbox))
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
  

if __name__ == "__main__":

  args,tech = parse_args()
  main( args, tech)
