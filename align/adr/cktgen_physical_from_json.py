from .cktgen import *

import json

def main(args, tech):
  
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

  netl = ADNetlist.fromPlacerResults( args.block_name, adts, placer_results)

  for wire in global_router_results['wires']:
    wire = convert_align_to_adr(wire)
    connected_pins = wire.get('connected_pins',None)
    # Enforce the new format
    assert connected_pins is not None

    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'], connected_pins=connected_pins)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
