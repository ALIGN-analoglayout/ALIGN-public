#!/usr/bin/python
import re
import json
import argparse
from datetime import datetime
from cell_fabric import Pdk
from pathlib import Path
pdkfile = (Path(__file__).parent / '../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_12nm_PDK_Abstraction.json').resolve()
with open((Path(__file__).parent / '../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_12nm_PDK_Abstraction.json').resolve(), "rt") as fp:
    j = json.load(fp)
def translate_data( macro_name, exclude_pattern, data, timestamp=None):
  gds_layer_tbl = { "nwell" : [4, 0],
                    "fin" : [2, 42], 	
                    "poly" : [1, 0], 	
                    "active" : [2, 0],	
                    "RVT" : [12, 164],	
                    "V0" : [12, 0],	
                    "M1" : [6, 0],
                    "V1" : [11, 0],
                    "M2" : [8, 0],
                    "V2" : [15, 0],
                    "V3" : [23, 0],
                    "M3" : [13, 0],
                    "M4" : [20, 0],
                    "cellarea" : [100, 0],
                    "BOUNDARY" : [100, 0],
                    "boundary" : [62, 21],
                    "bbox" : [100, 0],
                    "diearea" : [100, 0]
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

  lib = {"time" : tme, "libname" : "pcell", "units" : [ 0.00025, 2.5e-10 ]}
  libraries.append (lib)

  structures = []
  lib["bgnstr"] = structures


  def genVia( via, m_under, m_over, via_rect, m_under_rect, m_over_rect):
    nm = via_tbl[via]

    strct = {"time" : tme, "strname" : nm, "elements" : []}

    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[via][0], "datatype" : gds_layer_tbl[via][1],
                               "xy" : flat_rect_to_boundary( via_rect)})
    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[m_under][0], "datatype" : gds_layer_tbl[m_under][1],
                               "xy" : flat_rect_to_boundary( m_under_rect)})
    strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[m_over][0], "datatype" : gds_layer_tbl[m_over][1],
                               "xy" :  flat_rect_to_boundary( m_over_rect)})

    return strct

  via_tbl = { "V1": "M1V1M2_CDNS_562826669040_0", "V2": "M2V2M3_CDNS_562865774120_1"}


  structures.append( genVia( "V2", "M2", "M3",
                             [-180,-180,180,180], [-380,-180,380,180], [-180,-380,180,380]))

  structures.append( genVia( "V1", "M1", "M2",
                             [-180,-180,180,180], [-180,-380,180,380], [-380,-180,380,180]))

  strct = {"time" : tme, "strname" : macro_name, "elements" : []}
  structures.append (strct)
  
  def scale(x):
    
    result = x*4//j['ScaleFactor'] 
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

      strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl[obj['layer']][0],
                        "datatype" : gds_layer_tbl[obj['layer']][1],
                        "xy" : flat_rect_to_boundary( list(map(scale,obj['rect'])))})

  # vias 
  for obj in data['terminals']:
      if obj['layer'] not in via_tbl: continue
      if pat and pat.match( obj['netName']): continue

      r = list(map( scale, obj['rect']))
      xc = (r[0]+r[2])//2
      yc = (r[1]+r[3])//2

      strct["elements"].append ({"type": "sref", "sname" : via_tbl[obj['layer']], "xy" : [xc, yc]})

  strct["elements"].append ({"type": "boundary", "layer" : gds_layer_tbl['bbox'][0], "datatype" : gds_layer_tbl['bbox'][0],
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





