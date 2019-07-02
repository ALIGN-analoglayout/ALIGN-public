from .cktgen import *

#
# Need to rename these or the router crashes with an stoi error?
#
from .transformation import Rect as tRect
from .transformation import Transformation

import json
from collections import defaultdict



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

      gr_lst = [ [ int(t//(4*840)) for t in r.toList()] for r in lst]

      net_map[actual].append( (i,formal,gr_lst))

  wires = []
  for (k,v) in net_map.items():
    tmp = trivial_gr( k, v)
    wires += tmp

  return wires


if __name__ == "__main__":

  args,tech = parse_args()
  assert args.source != ''
  src = args.source


  assert args.placer_json != ''

  with open( args.placer_json, "rt") as fp:
    placer_results = json.load( fp)

  with open( f"INPUT/{src}_global_router_out.json", "rt") as fp:
    global_router_results = json.load( fp)

  wires = gr_hints(placer_results)
#  global_router_results = { "wires": wires}

  global_ycs2 = set()
  for leaf in placer_results['leaves']:

    ycs = set()
    ycs2 = set()
    ycs.add( leaf['bbox'][1])
    ycs.add( leaf['bbox'][3])
    ycs2.add( leaf['bbox'][1]%840)
    ycs2.add( leaf['bbox'][3]%840)

    for term in leaf['terminals']:
      ly = term['layer']
      term['layer'] = 'metal2' if ly == 'M2' else ly

      yc = (term['rect'][1]+term['rect'][3])//2
      ycs.add(yc)
      ycs2.add(yc%840)
      global_ycs2.add(yc%840)
#    print('XXX template_name',leaf['template_name'], ycs, ycs2)    
#  print('XXX', global_ycs2)


  ycs2 = set()
  for inst in placer_results['instances']:
    m840 = inst['transformation']['oY']%840
#    print(inst['instance_name'], m840)
    ycs2.add(m840)
#  print('Transform ycs2', ycs2)




  adts = {}

  for leaf in placer_results['leaves']:
    nm = leaf['template_name']
    adt = ADT( tech, nm, physical_bbox=leaf['bbox'])
    adts[nm] = adt

    for term in leaf['terminals']:
      adt.newWire( term['net_name'], Rect( *term['rect']), term['layer'])

  bbox = placer_results['bbox']

  netl = Netlist( nm=args.block_name, bbox=Rect( *bbox))
  adnetl =  ADNetlist( args.block_name)

  for inst in placer_results['instances']:
    tN = inst['template_name']
    iN = inst['instance_name']
    tr = inst['transformation']

#    print( tr)

    adnetl.addInstance( ADI( adts[tN], iN, ADITransform( tr['oX'], tr['oY'], tr['sX'], tr['sY'])))

    for (f,a) in inst['formal_actual_map'].items():
      adnetl.connect( iN, f, a)

  if 'ports' in placer_results:  
    ports = placer_results['ports']
    for p in ports:
      adnetl.addPort( p)

  adnetl.genNetlist( netl)

  for wire in global_router_results['wires']:
    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'])

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
