
from hier_design import load, dump

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

  adder_width = 64
  adder_height = 32

  place['bbox'][3] += adder_height

  pin_height = adder_height // 2

  ts = []
  fa_map = {}
  for p in [("l",16),("m",32),("r",48)]:
    for ty in [("n",0),("p",1)]:
      for net in [("ina",-1),("inb",1)]:
        net_name = "%s_%s_%s" % (p[0],ty[0],net[0])
        x = p[1]+net[1]
        y0 = ty[1]*pin_height + 1
        y1 =  ty[1]*pin_height + pin_height - 1
        ts.append( { "net_name": net_name, "layer": "metal3", "rect": [ x, y0, x, y1]})
        fa_map[net_name] = net_name

  adder_interface =  {
    "template_name" : "adder",
    "bbox": [ 0, 0, adder_width, adder_height],
    "terminals": ts
  }
  place['leaves'].append( adder_interface)

  place['instances'] = []

  place['instances'].append( {
    "instance_name": "adder",
    "template_name": "adder",
    "transformation": { "oX": 64, "oY": comp_and_diff_height + wcap_height, "sX": 1, "sY": 1},
    "formal_actual_map": fa_map
  })

  place['instances'].append( {
    "instance_name": "ctle",
    "template_name": "ctle",
    "transformation": { "oX": 0, "oY": comp_and_diff_height + wcap_height + adder_height, "sX": 1, "sY": 1},
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

    wcap_fa_map = {}
    for ty in ["p","n"]:
      for net in ["a","b"]:
        actual_name = "%s_%s_in%s" % (p[0],ty,net)
        formal_name = "cpl%s_%s" % (net,ty)
        wcap_fa_map[formal_name] = actual_name

    if p[0] == "m":
      wcap_fa_map["ina"] = "comp_outa"
      wcap_fa_map["inb"] = "comp_outb"
    else:
      wcap_fa_map["ina"] = "diff_%s_outa" % p[0]
      wcap_fa_map["inb"] = "diff_%s_outb" % p[0]

    place['instances'].append( {
      "instance_name": "wcap_%s" % p[0],
      "template_name": "wcap",
      "transformation": { "oX": ox, "oY": comp_and_diff_height, "sX": sx, "sY": 1},
      "formal_actual_map": wcap_fa_map
    })
  
    t_nm = "comp" if p[0] in "m" else "diff"
    i_nm = "%s_%s" % (t_nm, p[0])

    if t_nm == "comp":
      fa_map = {
        "sda_outa": "sda_outa",
        "sda_outb": "sda_outb",
        "outa": "comp_outa",
        "outb": "comp_outb"
      }
    else:
      fa_map = {
        "ina": "diff_%s_ina" % p[0],
        "inb": "diff_%s_inb" % p[0],
        "outa": "diff_%s_outa" % p[0],
        "outb": "diff_%s_outb" % p[0]
      }

    place['instances'].append( {
      "instance_name": i_nm,
      "template_name": t_nm,
      "transformation": { "oX": ox, "oY": 0, "sX": sx, "sY": 1},
      "formal_actual_map": fa_map
    })

  def gen_terminal_tbl( interface):
    tbl = {}
    for p in interface['terminals']:
      layer = p['layer']
      net_name = p['net_name']
      if layer not in tbl: tbl[layer] = {}
      if net_name not in tbl[layer]: tbl[layer][net_name] = []

      tbl[layer][net_name].append( p)
    return tbl

  wcap_terminal_tbl = gen_terminal_tbl( wcap_interface)
  adder_terminal_tbl = gen_terminal_tbl( adder_interface)

  print( adder_terminal_tbl)

  def find_routing_grids_covering_terminal( tbl, nm, layer):
    result = []
    for p in tbl[layer][nm]:
      xs = [ x//4 for x in p['rect']]
      result.append( xs)
    return result

  route = { "wires": []}

  gr_y_offset = (16*8) // 4

  for p in [("l",0),("m",1),("r",2)]:
    for ty in [("n",0),("p",1)]:
      for net in ["a","b"]:
        cpl_nm = "cpl%s_%s" % ( net, ty[0])

        m5_rects = find_routing_grids_covering_terminal( wcap_terminal_tbl, cpl_nm, "metal5")
        assert len(m5_rects) == 2
        xs = [ r[0] for r in m5_rects]

        print( p, ty, net, m5_rects, xs)

        net_name = "%s_%s_in%s" % (p[0], ty[0], net)

        m3_rects = find_routing_grids_covering_terminal( adder_terminal_tbl, net_name, "metal3")
        print( net_name, m3_rects)
        assert len(m3_rects)

        y0 = gr_y_offset + m5_rects[0][3]
        y1 = gr_y_offset + 88//4 + (m3_rects[0][1]+m3_rects[0][3])//2

        ox = p[1]*64//4
        print(ox,xs)

        for x in xs:
          assert 0 <= ox+x < 192//4, (ox,x,ox+x)

          route['wires'].append( {
            "layer": "metal5",
            "net_name": net_name,
            "width": 400,
            "rect": [ ox+x, y0, ox+x, y1]
          })

        other_x = m3_rects[0][0] + 64//4
        assert 0 <= other_x < 192//4, other_x

        all_xs = [ ox+x for x in xs] + [other_x]

        route['wires'].append( {
          "layer": "metal4",
          "net_name": net_name,
          "width": 400,
          "rect": [ min(all_xs), y1, max(all_xs), y1]
        })
    
  dump( "lane_placer_out_scaled.json", place)
  dump( "lane_global_router_out.json", route)

if __name__ == "__main__":
  main()
