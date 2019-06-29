from .cktgen import *

from .transformation import Rect, Transformation

import json
from collections import defaultdict

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
      lst = [trans.hitRect( Rect( *terminal['rect'])).canonical() for terminal in pin_map[formal]]

      gr_lst = [ [ int(round((t-2*840)/(4*840),2)) for t in r.toList()] for r in lst]

      net_map[actual].append( (i,formal,lst,gr_lst))

  for (k,v) in net_map.items():
    print(k)
    for x in v:
      print("   ", x)

if __name__ == "__main__":

  args,tech = parse_args()
  assert args.source != ''
  src = args.source

  assert args.placer_json != ''

  with open( args.placer_json, "rt") as fp:
    placer_results = json.load( fp)

#  with open( f"INPUT/{src}_global_router_out.json", "rt") as fp:
#    global_router_results = json.load( fp)
#  gr_hints(placer_results)


  wires = []
  wires.append( { 'layer': 'metal3', 'net_name': 'net3', 'width': 320, 'rect': [32,1,32,53]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net4', 'width': 320, 'rect': [30,10,30,40]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net4', 'width': 320, 'rect': [5,10,5,40]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net4', 'width': 320, 'rect': [5,20,30,20]})

  if False:
    wires.append( { 'layer': 'metal3', 'net_name': 'net4p', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'net5', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'net5p', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'net6', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'net6p', 'width': 320, 'rect': [32,1,32,53]})

    wires.append( { 'layer': 'metal3', 'net_name': 's0', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 's1', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 's2', 'width': 320, 'rect': [32,1,32,53]})

    wires.append( { 'layer': 'metal3', 'net_name': 'vga_out1', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'vga_out2', 'width': 320, 'rect': [32,1,32,53]})

    wires.append( { 'layer': 'metal3', 'net_name': 'vgnd', 'width': 320, 'rect': [32,1,32,53]})

    wires.append( { 'layer': 'metal3', 'net_name': 'vin1', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'vin2', 'width': 320, 'rect': [32,1,32,53]})

    wires.append( { 'layer': 'metal3', 'net_name': 'vmirror', 'width': 320, 'rect': [32,1,32,53]})
    wires.append( { 'layer': 'metal3', 'net_name': 'vps', 'width': 320, 'rect': [32,1,32,53]})

  global_router_results = { 'wires': wires}




  print( placer_results)
  print( global_router_results)


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
    print('XXX template_name',leaf['template_name'], ycs, ycs2)    
  print('XXX', global_ycs2)


  ycs2 = set()
  for inst in placer_results['instances']:
    m840 = inst['transformation']['oY']%840
    print(inst['instance_name'], m840)
    ycs2.add(m840)
  print('Transform ycs2', ycs2)




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

    print( tr)

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
