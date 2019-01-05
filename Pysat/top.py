
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

  t_place = {}
  t_place['nm'] = "top"
  t_place['bbox'] = [0,0,n_lanes*lane_width,lane_height]
  t_place['leaves'] = [ lane_interface]

  t_place['instances'] = []

  for i in range(n_lanes):
    i_nm = "lane_%d" % i

    t_place['instances'].append( {
      "instance_name": i_nm,
      "template_name": "lane",
      "transformation": { "oX": lane_width*i, "oY": 0, "sX": 1, "sY": 1},
      "formal_actual_map": {
      }
    })

  t_route = load( "top_global_router_out.json")

  dump( "top_placer_out_scaled.json", t_place)

if __name__ == "__main__":
  main()
