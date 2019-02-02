
from hier_design import load, dump
from copy import deepcopy

def main():
  s_place = load( "stack_placer_out_scaled.json")
  s_route = load( "stack_global_router_out.json")
  c_place = deepcopy(s_place)
  c_route = deepcopy(s_route)

  dp1x_interface = load( "dp1x_interface.json")['leaves'][0]
  dp2x_interface = load( "dp2x_interface.json")['leaves'][0]
  dp4x_interface = load( "dp4x_interface.json")['leaves'][0]
  mirrors_interface = load( "mirrors_interface.json")['leaves'][0]

  new_leaves = [ dp1x_interface,
                 dp2x_interface,
                 dp4x_interface,
                 mirrors_interface]

  c_place['nm'] = "wcap"
  c_place['leaves'] = new_leaves

  cunit_width = 16
  cunit_height = 16

  n_side_cols = 1

  c_place['leaves'].append(
    {
      "template_name" : "cunit",
      "bbox": [ 0, 0, cunit_width, cunit_height],
      "terminals": [
        { "net_name": "tp", "layer": "metal3", "rect": [ 1, 1, 1, cunit_height-1]},
        { "net_name": "tn", "layer": "metal3", "rect": [ 2, 1, 2, cunit_height-1]}
      ]
    }
    )

  stack_x_offset = cunit_width*n_side_cols

  # bump bounding box: one col on both sides
  c_place['bbox'][2] += 2*stack_x_offset

  metal2_kors = []
  b = c_place['bbox']
  print( b)
  for y in range(b[1]+1,b[3]):
    x0 = b[0]+1
    x1 = b[2]-1
    metal2_kors.append( {
      'net_name': '!kor',
      'layer': 'metal2',
      'rect': [x0,y,x1,y]
    })

#
# Disable for now
#
#  c_place['ports'] = metal2_kors
  c_place['ports'] = []

  # shift stack
  for inst in c_place['instances']:
    inst['transformation']['oX'] += stack_x_offset

  y_offset = 8+16

  def tup( ix, iy, side):
    assert side in ['l','r'], side

    idx = ix+iy
    i_nm = "cpl_%s_%d_%d" % (side,ix,iy)

    if side == 'r':
      idx = n_side_cols*4-1 - idx

# Make common centroid

# bp 3   an 3   
# ap 2   bn 2
# bn 1   ap 1
# an 0   bp 0

    suffix = "_n" if idx % 4 in [0,1] else "_p"
    if idx % 2 == 0:
      return ( i_nm, "outa", "cpla" + suffix)
    else:
      return ( i_nm, "outb", "cplb" + suffix)

  for (ix,iy) in ( (x,y) for y in range(4) for x in range(n_side_cols)):
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
    pair_sum = 2*xs[-1] + 8 + 1
    xs = xs + list( pair_sum - i for i in reversed(xs))

  print( "xs:", xs)

  for net in ["cpla_p","cplb_p","cpla_n","cplb_n"]:

    for x in xs:
      c_route['wires'].append({
        "layer": "metal5",
        "net_name": net,
        "width": 400,
        "rect": [x,8,x,tbin]
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
          wire['rect'][2] += 4*n_side_cols-2 + 1


  dump( "wcap_placer_out_scaled.json", c_place)
  dump( "wcap_global_router_out.json", c_route)

if __name__ == "__main__":
  main()
