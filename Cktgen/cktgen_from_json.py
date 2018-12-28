from cktgen import *
import json

if __name__ == "__main__":

  args,tech = parse_args()
  assert args.source != ''
  src = args.source

  assert args.placer_json != ''

  with open( args.placer_json, "rt") as fp:
    placer_results = json.load( fp)

  with open( "INPUT/%s_global_router_out.json" % src, "rt") as fp:
    global_router_results = json.load( fp)

#  print( placer_results)
#  print( global_router_results)

  def roundUp( x, f=2):
    assert x % f == 0
    result = f*((x+f-1)//f)
    assert x == result
    return result

  adts = {}

  for leaf in placer_results['leaves']:
    leaf_bbox = leaf['bbox']
    nm = leaf['template_name']

    # leaves x bbox is 1:1 with poly pitch
    # seems that number for rows is two (FIX this!)
    adt = ADT( tech, nm, npp=leaf_bbox[2], nr=(leaf_bbox[3]+3)//4)
    adts[nm] = adt

    for term in leaf['terminals']:
      r = term['rect']
      assert term['layer'] == "metal1"
      assert r[0] == r[2]
      adt.addM1Terminal( term['net_name'], r[0])

  # using half (the placer grid)    
  # HACK Dividing by 2
  def xg( x): 
    return tech.pitchPoly//2*tech.halfXGRGrid*x
  def yg( y): 
    return tech.pitchDG  //2*tech.halfYGRGrid*y

  bbox = placer_results['bbox']

  netl = Netlist( nm=args.block_name, bbox=Rect( 0,0, xg(roundUp(bbox[2])), yg(roundUp(bbox[3]))))
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
    netl.newGR( wire['net_name'], Rect( *wire['rect']), wire['layer'], wire['width'])

  pathlib.Path("INPUT").mkdir(parents=True, exist_ok=True)

  tech.write_files( "INPUT", netl.nm, netl.bbox.toList())
  netl.write_files( tech, "INPUT", args)
