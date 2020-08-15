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

  if timestamp is not None:
    ts = timestamp
  else:
    ts = datetime.datetime.now()

  top = "magic\ntech "+j1['Magic']['Techname']+"\ntimestamp "+ts+"\n"

  def scale(x):
    result = x*4//j1['ScaleFactor']//1000
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
      r=list(map(scale,obj['rect']))

      top+="<< "+j[k]['MagicLayerName']+" >>\n"
      top+="rect "+str(r[0])+" "+str(r[1])+" "+str(r[2])+" "+str(r[3])+"\n"
      #strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
      #                  "datatype" : j[k]['GdsDatatype']['Draw'],
      #                  "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})
      #if ('color' in obj):
      #    strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
      #                  "datatype" : j[k]['GdsDatatype'][obj['color']],
      #                  "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})
      if ('pin' in obj) and pinSwitch !=0:
          top+="pin "+j[k]['MagicLayerName']+" "+str(r[0])+" "+str(r[1])+" "+str(r[2])+" "+str(r[3])+"\n"
      #    strct["elements"].append ({"type": "boundary", "layer" : j[k]['GdsLayerNo'],
      #                  "datatype" : j[k]['GdsDatatype']['Pin'],
      #                  "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias
  for obj in data['terminals']:
      k = obj['layer']
      if k not in via_gen_tbl: continue
      if exclude_based_on_name( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2
      top+="<< "+j['Bbox']['MagicLayerName']+" >>\n"
      top+="rect "+str(r[0])+" "+str(r[1])+" "+str(r[2])+" "+str(r[3])+"\n"

      #strct["elements"].append ({"type": "sref", "sname" : via_gen_tbl[k][0], "xy" : [xc, yc]})

  #strct["elements"].append ({"type": "boundary", "layer" : j['Bbox']['GdsLayerNo'], "datatype" : j['Bbox']['GdsDatatype']['Draw'],
  # #                 "xy" : flat_rect_to_boundary( list(map(scale,data['bbox'])))})
  top+="<< end >>\n"
  return top

def translate( macro_name, exclude_pattern, pinSwitch, fp, ofile, timestamp=None, p=None):
  ofile.write(translate_data( macro_name, exclude_pattern, p.layerfile, pinSwitch, json.load(fp), {}, timestamp))
