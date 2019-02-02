
from hier_design import load, dump

def main():

  cunit_width = 16
  cunit_height = 16

  nx_cap = 12
  ny_cap = 12

  ctle_width = 192
  ctle_height = 192

  place = {}
  place['nm'] = "lane"
  place['bbox'] = [0,0,ctle_width,ctle_height]
  place['leaves'] = []

  assert place['bbox'][2] == cunit_width*nx_cap
  assert place['bbox'][3] == cunit_height*ny_cap

  place['leaves'].append(
    {
      "template_name" : "cunit",
      "bbox": [ 0, 0, cunit_width, cunit_height],
      "terminals": [
        { "net_name": "tp", "layer": "metal3", "rect": [ 1, 1, 1, cunit_height-1]},
        { "net_name": "tn", "layer": "metal3", "rect": [ 2, 1, 2, cunit_height-1]}
      ]
    }
  )

  place['instances'] = []

  for ix in range(nx_cap):
    for iy in range(ny_cap):
      i_nm = "icap_%d_%d" % (ix,iy)

      ox = ix*cunit_width
      sx = 1
      if ix < nx_cap//2:
        ox += cunit_width
        sx = -1

      place['instances'].append( {
        "instance_name": i_nm,
        "template_name": "cunit",
        "transformation": { "oX": ox, "oY": iy*cunit_height, "sX": sx, "sY": 1},
        "formal_actual_map": {
        }
      })

  route = load( "ctle_global_router_out.json")

  dump( "ctle_placer_out_scaled.json", place)

if __name__ == "__main__":
  main()
