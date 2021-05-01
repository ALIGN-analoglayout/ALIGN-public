#!/usr/bin/python
import re
import json
import datetime
from . import pdk
import logging
logger = logging.getLogger(__name__)

def translate_data( macro_name, exclude_pattern, pdkfile, pinSwitch, data, via_gen_tbl, timestamp=None):
  j = pdk.Pdk().load(pdkfile)
  with open(pdkfile, "rt") as fp1:
    j1 = json.load(fp1)
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
      strct["elements"].append ({"type": "boundary", "layer" : j[layer]['GdsLayerNo'], "datatype" : j[layer]['GdsDatatype']['Draw'],
                                 "xy" : flat_rect_to_boundary( rect)})

    return strct

  for via, (gen_name, layers) in via_gen_tbl.items():
    structures.append( createViaSref(via, gen_name, layers) )

  strct = {"time" : tme, "strname" : macro_name, "elements" : []}
  structures.append (strct)

  def scale(x):

      result = x*40//j1['ScaleFactor'] ### Multiplied by 40: Unit are set to 2.5e-11 and input is in 1e-09
    if isinstance(result, float):
      logger.warning(f"translate_data:scale: Coord {x} ({result}) not integral")
      intresult = int(round(result,0))
      assert abs(intresult-result) < 0.001
      return intresult
    else:
      return result


  pat = None
  if exclude_pattern != '':
    pat = re.compile( exclude_pattern)

  def exclude_based_on_name( nm):
    return pat and nm is not None and pat.match( nm)

  # non-vias
  for obj in data['terminals']:
      k = obj['layer']
      if k in via_gen_tbl: continue
      if exclude_based_on_name( obj['netName']): continue    
      r = list(map( scale, obj['rect']))

      if k == "V0" and (r[2]-r[0]) > scale(10*j['V0']['WidthX']):
          for NumX in range(j['GuardRing']['viaArray']):
              new_rect = [r[0]+NumX*(j['GuardRing']['v0WidthX']+j['GuardRing']['v0SpaceX']), r[1],
                          r[0]+NumX*(j['GuardRing']['v0WidthX']+j['GuardRing']['v0SpaceX'])+j['GuardRing']['v0WidthX'], r[3]]
              strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
                            "datatype" : j[k]['GdsDatatype']['Draw'],
                            "xy" : flat_rect_to_boundary( new_rect)})
      else:
          strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
                        "datatype" : j[k]['GdsDatatype']['Draw'],
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})
      if ('color' in obj):
          strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
                        "datatype" : j[k]['GdsDatatype'][obj['color']],
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})
      if ('pin' in obj) and pinSwitch !=0:
          strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
                        "datatype" : j[k]['GdsDatatype']['Pin'],
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias
  for obj in data['terminals']:
      k = obj['layer']
      if k not in via_gen_tbl: continue
      if exclude_based_on_name( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2
      
      strct["elements"].append ({"type": "sref", "sname" : via_gen_tbl[k][0], "xy" : [xc, yc]})

  strct["elements"].append ({"type": "boundary", "layer" : j['Bbox']['GdsLayerNo'], "datatype" : j['Bbox']['GdsDatatype']['Draw'],
                    "xy" : flat_rect_to_boundary( list(map(scale,data['bbox'])))})

  return top

def translate( macro_name, exclude_pattern, pinSwitch, fp, ofile, timestamp=None, p=None):
  json.dump(translate_data( macro_name, exclude_pattern, p.layerfile, pinSwitch, json.load(fp), {}, timestamp), ofile, indent=4)
