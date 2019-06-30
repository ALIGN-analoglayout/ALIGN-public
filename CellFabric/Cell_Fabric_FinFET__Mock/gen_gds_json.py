#!/usr/bin/python
import re
import json
import argparse
from datetime import datetime

def translate_data( macro_name, exclude_pattern, data, timestamp=None):

  gds_layer_tbl = { "nwell" : 1,
                    "fin" : 2, 	
                    "poly" : 3, 	
                    "GCUT" : 4,
                    "active" : 5,	
                    "SDT" : 6,	
                    "nselect" : 7,
                    "pselect" : 8,
                    "SLVT" : 9,	
                    "LVT" : 10,	                                                           
                    "polycon" : 11,
                    "V0" : 12,	
                    "M1" : 13,
                    "V1" : 14,
                    "M2" : 15,
                    "V2" : 16,
                    "V3" : 17,
                    "V4" : 18,
                    "M3" : 19,
                    #"V3" : 20,
                    "M4" : 21,
                    "V4" : 22,
                    "M5" : 23,
                    "V5" : 24,
                    "M6" : 25,
                    "V6" : 26,
                    "M7" : 27,
                    "V7" : 28,
                    "M8" : 29,
                    "V8" : 30,
                    "M9" : 31,
                    "V9" : 32,
                    "cellarea" : 100,
                    "BOUNDARY" : 100,
                    "boundary" : 100,
                    "bbox" : 100,
                    "diearea" : 100
                  }

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


  def genVia( via, m_under, m_over, via_rect, m_under_rect, m_over_rect):
    nm = via_tbl[via]

    strct = {"time" : tme, "strname" : nm, "elements" : []}

    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[via], "datatype" : 0,
                               "xy" : flat_rect_to_boundary( via_rect)})
    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[m_under], "datatype" : 0,
                               "xy" : flat_rect_to_boundary( m_under_rect)})
    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[m_over], "datatype" : 0,
                               "xy" :  flat_rect_to_boundary( m_over_rect)})

    return strct

  via_tbl = { "V1": "M2_M1_CDNS_543864435521", "V2": "M3_M2_CDNS_543864435520"}


  structures.append( genVia( "V2", "M2", "M3",
                             [-640,-640,640,640], [-1440,-640,1440,640], [-640,-1440,640,1440]))

  structures.append( genVia( "V1", "M1", "M2",
                             [-640,-640,640,640], [-640,-1440,640,1440], [-1440,-640,1440,640]))

  strct = {"time" : tme, "strname" : macro_name, "elements" : []}
  structures.append (strct)
  
  def scale(x):
    
    result = x*4
    if type(result) == float:
      #print("-W- gen_gds_json:translate_data: Coord %s (%s) not integral" % (str(x),str(result)))
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
      if obj['layer'] in via_tbl: continue
      if pat and pat.match( obj['netName']): continue

      strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[obj['layer']],
                        "datatype" : 0,
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias 
  for obj in data['terminals']:
      if obj['layer'] not in via_tbl: continue
      if pat and pat.match( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2

      strct["elements"].append ({"type": "sref", "sname" : via_tbl[obj['layer']], "xy" : [xc, yc]})

  strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl['bbox'], "datatype" : 5,
                    "xy" : flat_rect_to_boundary( list(map(scale,data['bbox'])))})

  return top

def translate( macro_name, exclude_pattern, fp, ofile, timestamp=None):
  json.dump(translate_data( macro_name, exclude_pattern, json.load(fp), timestamp), ofile, indent=4)

if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Convert design json to GDS JSON")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-j", "--json_file_name", type=str, required=True)
  parser.add_argument( "-e", "--exclude_pattern", type=str, default='')

  args = parser.parse_args()

  ofile = open (args.block_name + ".gds.json", 'wt')

  with open( args.json_file_name, "rt") as fp:
    translate( args.block_name, args.exclude_pattern, fp, ofile, timestamp=datetime.now())





