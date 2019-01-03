
import json
from copy import deepcopy

def load( fn):
  with open( fn, "rt") as fp:
    j = json.load( fp)
  return j

def dump( fn, j):
  with open( fn, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')

def main():
  s_place = load( "stack_placer_out_scaled.json")

  s_route = load( "stack_global_router_out.json")

  c_place = deepcopy(s_place)
  c_route = deepcopy(s_route)

  c_place['nm'] = "wcap"

  cunit_width = 16
  cunit_width_narrower = 14
  cunit_height = 16

  n_side_cols = 0
  n_top_rows = 0

  c_place['leaves'].append(
    {
      "template_name" : "cunit",
      "bbox": [ 0, 0, cunit_width, cunit_height],
      "terminals": [
        { "net_name": "tp", "layer": "metal3", "rect": [ 1, 0, 1, cunit_height]},
        { "net_name": "tn", "layer": "metal3", "rect": [ 2, 0, 2, cunit_height]}
      ]
    }
    )

  c_place['leaves'].append(
    {
      "template_name" : "cunit_narrower",
      "bbox": [ 0, 0, cunit_width_narrower, cunit_height],
      "terminals": [
        { "net_name": "tp", "layer": "metal3", "rect": [ 1, 0, 1, cunit_height]},
        { "net_name": "tn", "layer": "metal3", "rect": [ 2, 0, 2, cunit_height]}
      ]
    }
    )

  # bump bounding box: one col on both sides
  c_place['bbox'][2] += 2*cunit_width*n_side_cols

  # shift stack
  for inst in c_place['instances']:
    inst['transformation']['oX'] += cunit_width*n_side_cols

  y_offset = 8

  def tup(ix, iy ,side):
    assert side in ['l','r'], side
    idx = ix+iy + (0 if side == 'l' else 1)
    i_nm = "cpl_%s_%d_%d" % (side,ix,iy)
    if idx % 2 == 0:
      return ( i_nm, "outa", "cpla")
    else:
      return ( i_nm, "outb", "cplb")


  


  for (ix,iy) in ( (x,y) for y in range(5) for x in range(n_side_cols)):
    (i_nm, tp, tn) = tup( ix, iy, 'l')
    c_place['instances'].append({
      "instance_name": i_nm,
      "template_name": "cunit",
      "transformation": {
        "oX": cunit_width + ix*cunit_width,
        "oY": y_offset+iy*cunit_height,
        "sX": -1,
        "sY": 1
      },
      "formal_actual_map": {
        "tp": tp,
        "tn": tn
      }
    })

    (i_nm, tp, tn) = tup( ix, iy, 'r')
    c_place['instances'].append({
      "instance_name": i_nm,
      "template_name": "cunit",
      "transformation": { 
        "oX": cunit_width*n_side_cols + s_place['bbox'][2] + ix*cunit_width,
        "oY": y_offset+iy*cunit_height,
        "sX": 1,
        "sY": 1
      },
      "formal_actual_map": {
        "tp": tp,
        "tn": tn
      }
    })

  # routing grid is 4 placement pitches (poly pitches)

  assert cunit_width % 4 == 0

  shift = (n_side_cols*cunit_width) // 4

  for wire in c_route['wires']:
    wire['rect'][0] += shift 
    wire['rect'][2] += shift 

  tbin = (c_place['bbox'][3]-1)//4

  xs = [ 4*i+3 for i in range(n_side_cols)]
  if xs:
    pair_sum = 2*xs[-1] + 7 + 1
    xs = xs + list( pair_sum - i for i in reversed(xs))

  print( "xs:", xs)

  for net in ["cpla","cplb"]:

    for x in xs:
      c_route['wires'].append({
        "layer": "metal5",
        "net_name": net,
        "width": 400,
        "rect": [x,0,x,tbin]
      })
    if xs:
      c_route['wires'].append({
        "layer": "metal4",
        "net_name": net,
        "width": 400,
        "rect": [xs[0],tbin,xs[-1],tbin]
      })

  # extend the metal4 and metal5 grs on "outa" and "outb"
  for wire in c_route['wires']:
    if wire['net_name'] in ["outa","outb"]:
      if wire['layer'] == "metal4":
        if xs:
          wire['rect'][0] -= 4*n_side_cols-2
          wire['rect'][2] += 4*n_side_cols-2
      if wire['layer'] == "metal5":
        wire['rect'][1] = 2

  # add another
  for net in ["outa","outb"]:
    if xs:
      c_route['wires'].append({
        "layer": "metal4",
        "net_name": net,
        "width": 400,
        "rect": [xs[0],2,xs[-1],2]
      })


  dump( "wcap_placer_out_scaled.json", c_place)
  dump( "wcap_global_router_out.json", c_route)

if __name__ == "__main__":
  main()
