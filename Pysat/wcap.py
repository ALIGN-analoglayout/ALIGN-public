
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
  cunit_height = 16

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

  # bump bounding box: one col on both sides
  c_place['bbox'][2] += 2*cunit_width

  # shift stack
  for inst in c_place['instances']:
    inst['transformation']['oX'] += cunit_width

  y_offset = 8

  def tup(idx,side):
    if side == 'l':
      if idx % 2 == 0:
        return ("cpl_a_%d" % idx, "outa", "cpla")
      else:
        return ("cpl_b_%d" % idx, "outb", "cplb")
    elif side == 'r':
      if idx % 2 == 0:
        return ("cpl_b_%d" % idx, "outb", "cplb")
      else:
        return ("cpl_a_%d" % idx, "outa", "cpla")
    else:
      assert side in ['l','r'], side

  for idx in range(5):
    (i_nm, tp, tn) = tup( idx, 'l')

    c_place['instances'].append({
      "instance_name": i_nm,
      "template_name": "cunit",
      "transformation": {
        "oX": cunit_width,
        "oY": y_offset+idx*cunit_height,
        "sX": -1,
        "sY": 1
      },
      "formal_actual_map": {
        "tp": tp,
        "tn": tn
      }
    })

    (i_nm, tp, tn) = tup( idx, 'r')
    c_place['instances'].append({
      "instance_name": i_nm,
      "template_name": "cunit",
      "transformation": { 
        "oX": cunit_width + s_place['bbox'][2],
        "oY": y_offset+idx*cunit_height,
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

  shift = cunit_width // 4

  for wire in c_route['wires']:
    wire['rect'][0] += shift 
    wire['rect'][2] += shift 

  tbin = (c_place['bbox'][3]-1)//4

  for net in ["cpla","cplb"]:
    xs = [3,11]
    for x in xs:
      c_route['wires'].append({
        "layer": "metal5",
        "net_name": net,
        "width": 400,
        "rect": [x,0,x,tbin]
      })
    c_route['wires'].append({
      "layer": "metal4",
      "net_name": net,
      "width": 400,
      "rect": [xs[0],tbin,xs[1],tbin]
    })


  # extend the metal4 and metal5 grs on "outa" and "outb"
  for wire in c_route['wires']:
    if wire['net_name'] in ["outa","outb"]:
      if wire['layer'] == "metal4":
        wire['rect'][0] -= 2
        wire['rect'][2] += 2
      if wire['layer'] == "metal5":
        wire['rect'][1] = 2

  # add another
  for net in ["outa","outb"]:
    c_route['wires'].append({
      "layer": "metal4",
      "net_name": net,
      "width": 400,
      "rect": [3,2,11,2]
    })


  dump( "wcap_placer_out_scaled.json", c_place)
  dump( "wcap_global_router_out.json", c_route)

if __name__ == "__main__":
  main()
