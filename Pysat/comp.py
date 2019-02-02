
from hier_design import load, dump

def main():

  nx_input_cap = 4
  ny_input_cap = 2

  place = {}
  place['nm'] = "comp"
  place['bbox'] = [0,0,0,0]
  place['leaves'] = []

  cunit_width = 16
  cunit_height = 16

  sda_width = 64
  sda_height = 6*cunit_height

  place['bbox'][2] = nx_input_cap*cunit_width

  place['bbox'][3] += sda_height
  place['bbox'][3] += cunit_height*ny_input_cap

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

  place['leaves'].append(
    {
      "template_name" : "sda",
      "bbox": [ 0, 0, sda_width, sda_height],
      "terminals": [
        { "net_name": "outa", "layer": "metal3", "rect": [ 31, 5*cunit_height+1, 31, 6*cunit_height-1]},
        { "net_name": "outb", "layer": "metal3", "rect": [ 33, 5*cunit_height+1, 33, 6*cunit_height-1]}
      ]
    }
  )

  place['ports'] = [
    { "net_name": "outa", "layer": "metal5", "rect": [ 31, 7*cunit_height+1, 31, 8*cunit_height-1]},
    { "net_name": "outb", "layer": "metal5", "rect": [ 33, 7*cunit_height+1, 33, 8*cunit_height-1]}
  ]

  place['instances'] = []

  place['instances'].append( {
    "instance_name": "sda",
    "template_name": "sda",
    "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1},
    "formal_actual_map": {
      "outa": "sda_outa",
      "outb": "sda_outb"
    }
  })

  for ix in range(nx_input_cap):
    for iy in range(ny_input_cap):
      i_nm = "icap_%d_%d" % (ix,iy)

      ox = ix*cunit_width
      sx = 1
      if ix < nx_input_cap//2:
        ox += cunit_width
        sx = -1

      place['instances'].append( {
        "instance_name": i_nm,
        "template_name": "cunit",
        "transformation": { "oX": ox, "oY": sda_height + iy*cunit_height, "sX": sx, "sY": 1},
        "formal_actual_map": {
        }
      })

  route = load( "comp_global_router_out.json")

  dump( "comp_placer_out_scaled.json", place)

if __name__ == "__main__":
  main()
