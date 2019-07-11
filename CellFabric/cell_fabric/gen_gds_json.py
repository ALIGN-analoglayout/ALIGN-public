#!/usr/bin/python
import re
import json
import datetime

def translate_data( macro_name, exclude_pattern, data, gds_layer_tbl, via_gen_tbl, timestamp=None):

  def rect_to_boundary( r):
    ordering = [ (0,1), (0,3), (2,3), (2,1), (0,1)]
    return [ (r[p[0]],r[p[1]]) for p in ordering]

  def flat_rect_to_boundary( r):
    ordering = [ (0,1), (0,3), (2,3), (2,1), (0,1)]
    return [ r[p[i]] for p in ordering for i in range(0,2)]

  # Top JSON GDS structure
  libraries = []
  top = {"header" : 600, "bgnlib" : libraries}

  if timestamp is not None:
    ts = timestamp
  else:
    ts = datetime.datetime.now()

  tme = [ ts.year, ts.month, ts.day, ts.hour, ts.minute, ts.second]
  tme = tme + tme

  lib = {"time" : tme, "libname" : "pcell", "units" : [ 0.000025, 2.5e-11 ]}
  libraries.append (lib)

  structures = []
  lib["bgnstr"] = structures


  def createViaSref(via, nm, layers):

    strct = {"time" : tme, "strname" : nm, "elements" : []}

    for layer, rect in layers.items():
      strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[layer], "datatype" : 0,
                                 "xy" : flat_rect_to_boundary( rect)})

    return strct

  for via, (gen_name, layers) in via_gen_tbl.items():
    structures.append( createViaSref(via, gen_name, layers) )

  strct = {"time" : tme, "strname" : macro_name, "elements" : []}
  structures.append (strct)

  def scale(x):

    result = x*4
    if type(result) == float:
      print("-W- gen_gds_json:translate_data: Coord %s (%s) not integral" % (str(x),str(result)))
      intresult = int(result)
      assert abs(intresult-result) < 0.00001
      return intresult
    else:
      return result


  pat = None
  if exclude_pattern != '':
    pat = re.compile( exclude_pattern)

  # non-vias
  for obj in data['terminals']:
      if obj['layer'] in via_gen_tbl: continue
      if pat and pat.match( obj['netName']): continue

      strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[obj['layer']],
                        "datatype" : 0,
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias 
  for obj in data['terminals']:
      if obj['layer'] not in via_gen_tbl: continue
      if pat and pat.match( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2

      strct["elements"].append ({"type": "sref", "sname" : via_gen_tbl[obj['layer']][0], "xy" : [xc, yc]})

  strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl['bbox'], "datatype" : 5,
                    "xy" : flat_rect_to_boundary( list(map(scale,data['bbox'])))})

  return top

def translate( macro_name, exclude_pattern, fp, ofile, gds_layer_tbl, via_gen_tbl=None, timestamp=None):

  if via_gen_tbl is None:
    via_gen_tbl = {}

  json.dump(translate_data( macro_name, exclude_pattern, json.load(fp), gds_layer_tbl, via_gen_tbl, timestamp), ofile, indent=4)
