from cktgen.cktgen import *
import json

if __name__ == "__main__":

  args,tech = parse_args()


  with open( "INPUT/ota_bigger_placer_out.json", "rt") as fp:
    placer_results = json.load( fp)

  with open( "INPUT/ota_bigger_global_router_out.json", "rt") as fp:
    global_router_results = json.load( fp)

  def roundUp( x, f): return f*((x+f-1)//f)

  print( placer_results)
  print( global_router_results)

  adts = {}

  for leaf in placer_results['leaves']:
    leaf_bbox = leaf['bbox']
    nm = leaf['template_name']

    adt = ADT( tech, nm, npp=2*leaf_bbox[2], nr=(leaf_bbox[3]+1)//2)
    adts[nm] = adt

    for term in leaf['terminals']:
      r = term['rect']
      assert term['layer'] == "metal1"
      assert r[0] == r[2]
      adt.addM1Terminal( term['net_name'], 2*r[0])

  # using half (the placer grid)
  def xg( x): 
    return tech.pitchPoly*tech.halfXGRGrid*x
  def yg( y): 
    return tech.pitchDG  *tech.halfYGRGrid*y

  bbox = placer_results['bbox']

  # Global router units
  print( 'placer', bbox)

  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg( roundUp(bbox[2],2)), yg( roundUp(bbox[3],2))))
  adnetl =  ADNetlist( args.block_name)

  for inst in placer_results['instances']:
    tN = inst['template_name']
    iN = inst['instance_name']
    tr = inst['transformation']

    print( tr)

    adnetl.addInstance( ADI( adts[tN], iN, ADITransform( xg(tr['oX']), yg(tr['oY']), tr['sX'], tr['sY'])))

    for (f,a) in inst['formal_actual_map'].items():
      adnetl.connect( iN, f, a)

  adnetl.genNetlist( netl)

  for wire in global_router_results['wires']:
    # these are in Global router units
    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'])

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
