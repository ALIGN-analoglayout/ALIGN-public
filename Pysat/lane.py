
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
  comp_interface = load( "comp_interface.json")['leaves'][0]
  diff_interface = load( "diff_interface.json")['leaves'][0]


  comp_and_diff_width = 64
  comp_and_diff_height = 128

  assert comp_interface['bbox'][2] == comp_and_diff_width
  assert diff_interface['bbox'][2] == comp_and_diff_width

  assert comp_interface['bbox'][3] == comp_and_diff_height
  assert diff_interface['bbox'][3] == comp_and_diff_height
  
  wcap_width = wcap_interface['bbox'][2]
  wcap_height = wcap_interface['bbox'][3]

  place = {}
  place['nm'] = "lane"
  place['bbox'] = [0,0,3*wcap_width,wcap_height]
  place['leaves'] = [ wcap_interface, comp_interface, diff_interface]

  assert place['bbox'][2] == 192
  assert place['bbox'][3] == 88

  place['bbox'][3] += comp_and_diff_height

  ctle_interface = load( "ctle_interface.json")['leaves'][0]

  ctle_width = ctle_interface['bbox'][2]
  ctle_height = ctle_interface['bbox'][3]

  place['leaves'].append( ctle_interface)
  place['bbox'][3] += ctle_height

  place['instances'] = []

  place['instances'].append( {
    "instance_name": "ctle",
    "template_name": "ctle",
    "transformation": { "oX": 0, "oY": comp_and_diff_height + wcap_height, "sX": 1, "sY": 1},
    "formal_actual_map": {
    }
  })


  pairs = [("l", 0), ("m", 64), ("r", 128)]

  for p in pairs:
    ox = p[1]
    sx = 1
    if p[0] == "r":
      ox += comp_and_diff_width
      sx = -1

    place['instances'].append( {
      "instance_name": "wcap_%s" % p[0],
      "template_name": "wcap",
      "transformation": { "oX": ox, "oY": comp_and_diff_height, "sX": sx, "sY": 1},
      "formal_actual_map": {
      }
    })
  
    t_nm = "comp" if p[0] in "m" else "diff"
    i_nm = "%s_%s" % (t_nm, p[0])

    if t_nm == "comp":
      fa_map = {
        "sda_outa": "sda_outa",
        "sda_outb": "sda_outb"#,
#        "outa": "comp_outa",
#        "outb": "comp_outb"
      }
    else:
      fa_map = {
        "ina": "diff_%s_ina" % p[0],
        "inb": "diff_%s_inb" % p[0]#,
#        "outa": "diff_%s_outa" % p[0],
#        "outb": "diff_%s_outa" % p[0]
      }

    place['instances'].append( {
      "instance_name": i_nm,
      "template_name": t_nm,
      "transformation": { "oX": ox, "oY": 0, "sX": sx, "sY": 1},
      "formal_actual_map": fa_map
    })

  route = load( "lane_global_router_out.json")

  dump( "lane_placer_out_scaled.json", place)

if __name__ == "__main__":
  main()
