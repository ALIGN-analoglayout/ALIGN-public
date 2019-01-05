
import json

def load( fn):
  with open( fn, "rt") as fp:
    j = json.load( fp)
  return j

def dump( fn, j):
  with open( fn, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')

def main():

  wcap_interface = load( "wcap_interface.json")['leaves'][0]


  nx_input_cap = 4
  ny_input_cap = 8

  wcap_width = wcap_interface['bbox'][2]
  wcap_height = wcap_interface['bbox'][3]

  l_place = {}
  l_place['nm'] = "lane"
  l_place['bbox'] = [0,0,3*wcap_width,wcap_height]
  l_place['leaves'] = [ wcap_interface]

  assert l_place['bbox'][2] == 192
  assert l_place['bbox'][3] == 88

  cunit_width = 16
  cunit_height = 16

  assert nx_input_cap*cunit_width*3 == l_place['bbox'][2]

  wcap_y_offset = cunit_height*ny_input_cap

  l_place['bbox'][3] += wcap_y_offset

  l_place['leaves'].append(
    {
      "template_name" : "cunit",
      "bbox": [ 0, 0, cunit_width, cunit_height],
      "terminals": [
        { "net_name": "tp", "layer": "metal3", "rect": [ 1, 1, 1, cunit_height-1]},
        { "net_name": "tn", "layer": "metal3", "rect": [ 2, 1, 2, cunit_height-1]}
      ]
    }
  )

  ctle_interface = load( "ctle_interface.json")['leaves'][0]

  ctle_width = ctle_interface['bbox'][2]
  ctle_height = ctle_interface['bbox'][3]

  l_place['leaves'].append( ctle_interface)
  l_place['bbox'][3] += ctle_height

  l_place['instances'] = []

  l_place['instances'].append( {
    "instance_name": "ctle",
    "template_name": "ctle",
    "transformation": { "oX": 0, "oY": wcap_y_offset + wcap_height, "sX": 1, "sY": 1},
    "formal_actual_map": {
    }
  })

  pairs = [("wcap_l", 0), ("wcap_m", 64), ("wcap_r", 128)]

  for p in pairs:
    l_place['instances'].append( {
      "instance_name": p[0],
      "template_name": "wcap",
      "transformation": { "oX": p[1], "oY": wcap_y_offset, "sX": 1, "sY": 1},
      "formal_actual_map": {
      }
    })
  
    for ix in range(nx_input_cap):
      for iy in range(ny_input_cap):
        i_nm = "icap_%s_%d_%d" % (p[0],ix,iy)

        ox = p[1] + ix*cunit_width
        sx = 1
        if ix < nx_input_cap//2:
          ox += cunit_width
          sx = -1

        l_place['instances'].append( {
          "instance_name": i_nm,
          "template_name": "cunit",
          "transformation": { "oX": ox, "oY": iy*cunit_height, "sX": sx, "sY": 1},
          "formal_actual_map": {
          }
        })

  l_route = load( "lane_global_router_out.json")

  dump( "lane_placer_out_scaled.json", l_place)

if __name__ == "__main__":
  main()
