
import json

def load( fn):
  with open( fn, "rt") as fp:
    j = json.load( fp)
  return j

def dump( fn, j):
  with open( fn, "wt") as fp:
    fp.write( json.dumps( j, indent=2) + '\n')

def main():

  lane_interface = load( "lane_interface.json")['leaves'][0]

  n_lanes = 4

  lane_width = lane_interface['bbox'][2]
  lane_height = lane_interface['bbox'][3]

  place = {}
  place['nm'] = "top"
  place['bbox'] = [0,0,n_lanes*lane_width,lane_height]
  place['leaves'] = [ lane_interface]

  place['instances'] = []

  route = { "wires": []}

  for i in range(n_lanes):
    i_nm = "lane_%d" % i

    fa_map = {
      "sda_outa": "lane_%d_sda_outa" % i,
      "sda_outb": "lane_%d_sda_outb" % i
    }

    if i < n_lanes-1:
      fa_map["diff_r_ina"] = "lane_%d_sda_outa" % (i+1)
      fa_map["diff_r_inb"] = "lane_%d_sda_outb" % (i+1)

    if i > 0:
      fa_map["diff_l_ina"] = "lane_%d_sda_outa" % (i-1)
      fa_map["diff_l_inb"] = "lane_%d_sda_outb" % (i-1)

    place['instances'].append( {
      "instance_name": i_nm,
      "template_name": "lane",
      "transformation": { "oX": lane_width*i, "oY": 0, "sX": 1, "sY": 1},
      "formal_actual_map": fa_map
    })


    ry = 22

    rx0 = (i * lane_width + lane_width // 2) // 4
    rx1 = (i * lane_width + lane_width // 2) // 4

    if i < n_lanes-1:
      rx1 += 25 #lane_width // 8 ish
    else:
      rx1 += 2
    if i > 0:
      rx0 -= 25 #lane_width // 8 ish
    else:
      rx0 -= 2

    for net in ["outa","outb"]:
      net_nm = "lane_%d_sda_%s" % (i,net)

      route['wires'].append( {
        "net_name": net_nm,
        "layer": "metal4",
        "width": 400,
        "rect": [rx0,ry,rx1,ry]
      })

  dump( "top_placer_out_scaled.json", place)
  dump( "top_global_router_out.json", route)


if __name__ == "__main__":
  main()
