import json
import pathlib

from .ad import ADNetlist
from .converters import convert_align_to_adr
from ..cell_fabric.transformation import Rect

def main(args, tech):
  #
  # Need to get this from layers.json
  #
  metal_layer_map = { f'M{i}' : f'metal{i}' for i in range(0,7) }
  via_layer_map = { f'V{i}' : f'via{i}' for i in range(0,6) }
  layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))

  assert args.placer_json != ''
  with open( args.placer_json, "rt") as fp:
    placer_results = json.load( fp)

  netl = ADNetlist.fromPlacerResults( args.block_name, tech, layer_map, placer_results)

  if args.gr_json != '':
    gr_fn = args.gr_json
  else:
    assert args.source != ''
    gr_fn = f"INPUT/{args.source}_global_router_out.json"

  with open( gr_fn, "rt") as fp:
    global_router_results = json.load( fp)

  for wire in global_router_results['wires']:
    wire = convert_align_to_adr(wire)
    connected_pins = wire.get('connected_pins',None)
    # Enforce the new format
    assert connected_pins is not None

    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'], connected_pins=connected_pins)

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
