#!/usr/bin/python
import re
import json
import argparse
import datetime

if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Convert design json to GDS JSON")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-j", "--json_file_name", type=str, required=True)
  parser.add_argument( "-e", "--exclude_pattern", type=str, default='')

  args = parser.parse_args()

  gds_layer_tbl = { "nwell" : 1,
                    "fin" : 2, 	
                    "poly" : 7, 	
                    "GCUT" : 10,
                    "active" : 11,	
                    "RVT" : 88,	
                    "nselect" : 12,
                    "pselect" : 13,
                    "SLVT" : 97,	
                    "LVT" : 98,	
                    "SRAMDRC" : 99,
                    "SRAMVT" : 110,
                    "DUMMY" : 8,
                    "polycon" : 16,
                    "LISD" : 17,
                    "via0" : 18,
                    "M0"   : 98,
                    "M1" : 19,
                    "via1" : 21,
                    "M2" : 20,
                    "via2" : 25,
                    "via3" : 35,
                    "via4" : 45,
                    "M3" : 30,
                    "V3" : 35,
                    "M4" : 40,
                    "V4" : 45,
                    "M5" : 50,
                    "V5" : 55,
                    "M6" : 60,
                    "V6" : 65,
                    "M7" : 70,
                    "V7" : 75,
                    "M8" : 80,
                    "V8" : 85,
                    "M9" : 90,
                    "V9" : 95,
                    "Pad" : 96,
                    "cellarea" : 100,
                    "BOUNDARY" : 100,
                    "diearea" : 100
                  }

  with open( args.json_file_name, "rt") as fp:
    j = json.load( fp)

  def s( x):
    return "%.3f" % (x/1000.0)

  def rect_to_boundary( r):
    ordering = [ (0,1), (0,3), (2,3), (2,1), (0,1)]
    return [ (r[p[0]],r[p[1]]) for p in ordering]

  def flat_rect_to_boundary( r):
    ordering = [ (0,1), (0,3), (2,3), (2,1), (0,1)]
    return [ r[p[i]] for p in ordering for i in range(0,2)]

  # Top JSON GDS structure
  libraries = []
  top = {"header" : 600, "bgnlib" : libraries}
  now = datetime.datetime.now()
  tme = [ now.year, now.month, now.day, now.hour, now.minute, now.second,
          now.year, now.month, now.day, now.hour, now.minute, now.second]


  macro_name = args.block_name

  lib = {"time" : tme, "libname" : "pcell", "units" : [ 0.000025, 2.5e-11 ]}
  libraries.append(lib)

  structures = []
  lib["bgnstr"] = structures

  str = {"time" : tme, "strname" : "M3_M2_CDNS_543864435520"}
  structures.append(str)
  elements = []
  str["elements"] = elements

  elements.append ({"type": "boundary", "layer" : 25, "datatype" : 0,
                    "xy" : flat_rect_to_boundary( [-640,-640,640,640])})
  elements.append ({"type": "boundary", "layer" : 20, "datatype" : 0,
                    "xy" : flat_rect_to_boundary( [-1440,-640,1440,640])})
  elements.append ({"type": "boundary", "layer" : 30, "datatype" : 0,
                    "xy" :  flat_rect_to_boundary( [-640,-1440,640,1440])})

  str = {"time" : tme, "strname" : "M2_M1_CDNS_543864435521"}
  structures.append(str)
  elements = []
  str["elements"] = elements

  elements.append ({"type": "boundary", "layer" : 21, "datatype" : 0,
                    "xy" : flat_rect_to_boundary( [-640,-640,640,640])})
  elements.append ({"type": "boundary", "layer" : 19, "datatype" : 0,
                    "xy" : flat_rect_to_boundary( [-640,-1440,640,1440])})
  elements.append ({"type": "boundary", "layer" : 20, "datatype" : 0,
                    "xy" : flat_rect_to_boundary( [-1440,-640,1440,640])})

  str = {"time" : tme, "strname" : macro_name}
  structures.append(str)
  elements = []
  str["elements"] = elements
  
  def scale(x): return x*4

  pat = None
  if args.exclude_pattern != '':
    pat = re.compile( args.exclude_pattern)

  via_tbl = { "via1": "M2_M1_CDNS_543864435521", "via2": "M3_M2_CDNS_543864435520"}

  # non-vias
  for obj in j['terminals']:
      if obj['layer'] in via_tbl: continue
      if pat and pat.match( obj['netName']): continue

      elements.append ({"type": "boundary", "layer" : gds_layer_tbl[obj['layer']],
                        "datatype" : 0,
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias 
  for obj in j['terminals']:
      if obj['layer'] not in via_tbl: continue
      if pat and pat.match( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2

      elements.append ({"type": "sref", "sname" : via_tbl[obj['layer']], "xy" : [xc, yc]})

  elements.append ({"type": "boundary", "layer" : 235, "datatype" : 5,
                    "xy" : flat_rect_to_boundary( list(map(scale,j['bbox'])))})

  ofile = open (args.block_name + ".gds.json", 'wt')
  json.dump(top, ofile, indent=4)
