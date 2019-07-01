from .cktgen import *

#
# Need to rename these or the router crashes with an stoi error?
#
from .transformation import Rect as tRect
from .transformation import Transformation as tTransformation

import json
from collections import defaultdict

"""
vgnd
    ('C1', 'MINUS', [[9, 50, 16, 50]])
    ('C2', 'MINUS', [[39, 50, 46, 50]])
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'S', [[18, 0, 36, 0], [18, 2, 36, 3], [18, 5, 36, 5], [18, 7, 36, 8], [18, 10, 36, 10], [18, 12, 36, 13], [18, 15, 36, 15], [18, 17, 36, 18]])
vga_out1
    ('C1', 'PLUS', [[9, 43, 16, 43]])
    ('R0', 'MINUS', [[0, 48, 0, 49]])
    ('xM20|MN0_xM21|MN0', 'D1', [[18, 20, 36, 21], [18, 23, 36, 23], [18, 25, 36, 26], [18, 28, 36, 28]])
    ('xM30|MN0_xM31|MN0', 'D1', [[13, 31, 42, 31], [13, 33, 42, 34], [13, 36, 42, 36], [13, 38, 42, 39], [13, 41, 42, 41]])
    ('xM10|MN0_xM11|MN0', 'D1', [[18, 47, 36, 47], [18, 44, 36, 45]])
    ('xM00|MN0_xM01|MN0', 'D1', [[18, 52, 36, 53], [18, 50, 36, 50]])
vga_out2
    ('C2', 'PLUS', [[39, 43, 46, 43]])
    ('R1', 'MINUS', [[55, 48, 55, 49]])
    ('xM20|MN0_xM21|MN0', 'D2', [[18, 21, 36, 21], [18, 23, 36, 24], [18, 26, 36, 26], [18, 28, 36, 29]])
    ('xM30|MN0_xM31|MN0', 'D2', [[13, 31, 42, 32], [13, 34, 42, 34], [13, 36, 42, 37], [13, 39, 42, 39], [13, 41, 42, 42]])
    ('xM10|MN0_xM11|MN0', 'D2', [[18, 46, 36, 47], [18, 44, 36, 44]])
    ('xM00|MN0_xM01|MN0', 'D2', [[18, 52, 36, 52], [18, 49, 36, 50]])
net5
    ('Nsw0', 'D', [[1, 44, 8, 44], [1, 46, 8, 46], [1, 49, 8, 49], [1, 51, 8, 51]])
    ('xM10|MN0_xM11|MN0', 'S', [[18, 47, 36, 47], [18, 45, 36, 45]])
s0
    ('Nsw0', 'G', [[1, 43, 8, 43], [1, 46, 8, 46], [1, 48, 8, 48], [1, 51, 8, 51]])
net5p
    ('Nsw0', 'S', [[1, 43, 8, 44], [1, 46, 8, 46], [1, 48, 8, 49], [1, 51, 8, 51]])
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'D3', [[18, 1, 36, 1], [18, 3, 36, 4], [18, 6, 36, 6], [18, 8, 36, 9], [18, 11, 36, 11], [18, 13, 36, 14], [18, 16, 36, 16], [18, 18, 36, 19]])
net4
    ('Nsw1', 'D', [[0, 20, 6, 21], [0, 23, 6, 23], [0, 25, 6, 26], [0, 28, 6, 28]])
    ('xM20|MN0_xM21|MN0', 'S', [[18, 20, 36, 20], [18, 23, 36, 23], [18, 25, 36, 25], [18, 28, 36, 28]])
s1
    ('Nsw1', 'G', [[0, 20, 6, 20], [0, 22, 6, 23], [0, 25, 6, 25], [0, 27, 6, 28]])
net4p
    ('Nsw1', 'S', [[0, 20, 6, 20], [0, 23, 6, 23], [0, 25, 6, 25], [0, 28, 6, 28]])
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'D4', [[18, 1, 36, 1], [18, 4, 36, 4], [18, 6, 36, 6], [18, 9, 36, 9], [18, 11, 36, 11], [18, 14, 36, 14], [18, 16, 36, 16], [18, 19, 36, 19]])
net6
    ('Nsw2', 'D', [[1, 31, 8, 31], [1, 33, 8, 34], [1, 36, 8, 36], [1, 38, 8, 39]])
    ('xM30|MN0_xM31|MN0', 'S', [[13, 31, 42, 31], [13, 33, 42, 33], [13, 36, 42, 36], [13, 38, 42, 38], [13, 41, 42, 41]])
s2
    ('Nsw2', 'G', [[1, 30, 8, 31], [1, 33, 8, 33], [1, 35, 8, 36], [1, 38, 8, 38]])
net6p
    ('Nsw2', 'S', [[1, 31, 8, 31], [1, 33, 8, 33], [1, 36, 8, 36], [1, 38, 8, 38]])
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'D2', [[18, 1, 36, 1], [18, 3, 36, 3], [18, 6, 36, 6], [18, 8, 36, 8], [18, 11, 36, 11], [18, 13, 36, 13], [18, 16, 36, 16], [18, 18, 36, 18]])
vps
    ('R0', 'PLUS', [[0, 51, 1, 51]])
    ('R1', 'PLUS', [[54, 51, 54, 51]])
vmirror
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'D0', [[18, 0, 36, 0], [18, 3, 36, 3], [18, 5, 36, 5], [18, 8, 36, 8], [18, 10, 36, 10], [18, 13, 36, 13], [18, 15, 36, 15], [18, 18, 36, 18]])
net3
    ('xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0', 'D1', [[18, 0, 36, 1], [18, 3, 36, 3], [18, 5, 36, 6], [18, 8, 36, 8], [18, 10, 36, 11], [18, 13, 36, 13], [18, 15, 36, 16], [18, 18, 36, 18]])
    ('xM00|MN0_xM01|MN0', 'S', [[18, 53, 36, 53], [18, 50, 36, 50]])
vin1
    ('xM20|MN0_xM21|MN0', 'G1', [[18, 20, 36, 20], [18, 22, 36, 23], [18, 25, 36, 25], [18, 27, 36, 28]])
    ('xM30|MN0_xM31|MN0', 'G1', [[13, 30, 42, 31], [13, 33, 42, 33], [13, 35, 42, 36], [13, 38, 42, 38], [13, 40, 42, 41]])
    ('xM10|MN0_xM11|MN0', 'G1', [[18, 47, 36, 48], [18, 45, 36, 45]])
    ('xM00|MN0_xM01|MN0', 'G1', [[18, 53, 36, 53], [18, 50, 36, 51]])
vin2
    ('xM20|MN0_xM21|MN0', 'G2', [[18, 21, 36, 21], [18, 23, 36, 23], [18, 26, 36, 26], [18, 28, 36, 28]])
    ('xM30|MN0_xM31|MN0', 'G2', [[13, 31, 42, 31], [13, 34, 42, 34], [13, 36, 42, 36], [13, 39, 42, 39], [13, 41, 42, 41]])
    ('xM10|MN0_xM11|MN0', 'G2', [[18, 47, 36, 47], [18, 44, 36, 44]])
    ('xM00|MN0_xM01|MN0', 'G2', [[18, 52, 36, 52], [18, 50, 36, 50]])
"""


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
    trans = tTransformation( tr['oX'], tr['oY'], tr['sX'], tr['sY'])

    for (formal,actual) in inst['formal_actual_map'].items():
      assert formal in pin_map
      lst = [trans.hitRect( tRect( *terminal['rect'])).canonical() for terminal in pin_map[formal]]

      gr_lst = [ [ int(round((t-2*840)/(4*840),2)) for t in r.toList()] for r in lst]

      net_map[actual].append( (i,formal,gr_lst))

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
  gr_hints(placer_results)


  wires = []
  wires.append( { 'layer': 'metal4', 'net_name': 'vgnd', 'width': 320, 'rect': [16,50,39,50]})
  wires.append( { 'layer': 'metal3', 'net_name': 'vgnd', 'width': 320, 'rect': [32,0,32,50]})

  wires.append( { 'layer': 'metal3', 'net_name': 'vga_out1', 'width': 320*3, 'rect': [30,20,30,53]})
  wires.append( { 'layer': 'metal4', 'net_name': 'vga_out1', 'width': 320*3, 'rect': [16,43,30,43]})
  wires.append( { 'layer': 'metal4', 'net_name': 'vga_out1', 'width': 320*3, 'rect': [0,49,31,49]})

  wires.append( { 'layer': 'metal3', 'net_name': 'vga_out2', 'width': 320*3, 'rect': [32,20,32,53]})
  wires.append( { 'layer': 'metal4', 'net_name': 'vga_out2', 'width': 320*3, 'rect': [32,43,39,43]})
  wires.append( { 'layer': 'metal4', 'net_name': 'vga_out2', 'width': 320*3, 'rect': [32,48,55,48]})



  wires.append( { 'layer': 'metal3', 'net_name': 'net3', 'width': 320, 'rect': [32,1,32,53]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net4', 'width': 320, 'rect': [30,10,30,40]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net4', 'width': 320, 'rect': [5,10,5,40]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net4', 'width': 320, 'rect': [5,20,30,20]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net4p', 'width': 320, 'rect': [30,1,30,20]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net4p', 'width': 320, 'rect': [3,20,3,28]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net4p', 'width': 320, 'rect': [3,20,30,20]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net5', 'width': 320, 'rect': [26,45,26,48]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net5', 'width': 320, 'rect': [4,44,4,52]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net5', 'width': 320, 'rect': [4,48,26,48]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net5p', 'width': 320, 'rect': [26,1,26,30]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net5p', 'width': 320, 'rect': [4,30,4,51]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net5p', 'width': 320, 'rect': [4,30,26,30]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net6', 'width': 320, 'rect': [26,31,26,41]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net6', 'width': 320, 'rect': [5,31,5,39]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net6', 'width': 320, 'rect': [5,35,26,35]})

  wires.append( { 'layer': 'metal3', 'net_name': 'net6p', 'width': 320, 'rect': [26,1,26,25]})
  wires.append( { 'layer': 'metal3', 'net_name': 'net6p', 'width': 320, 'rect': [3,25,3,39]})
  wires.append( { 'layer': 'metal4', 'net_name': 'net6p', 'width': 320, 'rect': [3,25,26,25]})


  wires.append( { 'layer': 'metal4', 'net_name': 'vps',  'width': 320, 'rect': [1,51,54,51]})  

  wires.append( { 'layer': 'metal3', 'net_name': 'vmirror',  'width': 320, 'rect': [27,0,27,18]})  

  wires.append( { 'layer': 'metal3', 'net_name': 's0',  'width': 320, 'rect': [5,43,5,51]})  
  wires.append( { 'layer': 'metal3', 'net_name': 's1',  'width': 320, 'rect': [3,20,3,28]})  
  wires.append( { 'layer': 'metal3', 'net_name': 's2',  'width': 320, 'rect': [5,31,5,38]})  

  wires.append( { 'layer': 'metal3', 'net_name': 'vin1',  'width': 320, 'rect': [27,20,27,53]})  
  wires.append( { 'layer': 'metal3', 'net_name': 'vin2',  'width': 320, 'rect': [27,20,27,53]})  

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
