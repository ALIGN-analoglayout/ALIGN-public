#!/usr/bin/env python
import json
import argparse
from datetime import datetime
from cell_fabric import gen_gds_json, pdk

from pathlib import Path
pdkfile = (Path(__file__).parent / 'layers.json').resolve()
with open(pdkfile, "rt") as fp1:
    j = json.load(fp1)
ScaleFactor = j['ScaleFactor']
def translate( macro_name, exclude_pattern, fp, ofile, timestamp=None, p=None):
  if p is None:
    p = pdk.Pdk().load(pdkfile)
  gds_layer_map = p.get_gds_map()

  gds_layer_map.update( {
          "nwellDraw": [1, 0],
          "finDraw": [2, 0],
          "polyDraw": [3, 0],
          "GCUTDraw": [4, 0],
          "activeDraw": [5, 0],
          "SDTDraw" : [6, 0],
          "nselectDraw" : [7, 0],
          "pselectDraw" : [8, 0],
          "SLVTDraw" : [9, 0],
          "LVTDraw" : [10, 0],
          "LISDDraw": [98, 0],
          "polyconDraw": [11, 0],
          "pcDraw": [99, 0],
          "pbDraw": [150, 0],
          "cellarea" : 100,
          "BOUNDARY" : 100,
          "boundaryDraw" : [100, 0],
          "bbox" : [100, 5],
          "diearea" : 100
      } )

  via_gen_tbl = {
      "V2Draw": (
          "M3_M2_CDNS_543864435520",
          {
          "V2Draw": [-640,-640,640,640],
          "M2Draw": [-1440,-640,1440,640],
          "M3Draw": [-640,-1440,640,1440]
          }
      ),
      "V1Draw": (
          "M2_M1_CDNS_543864435521",
          {
          "V1Draw": [-640,-640,640,640],
          "M1Draw": [-640,-1440,640,1440],
          "M2Draw": [-1440,-640,1440,640]
          }
      )
  }

  return gen_gds_json.translate(macro_name, exclude_pattern, ScaleFactor, fp, ofile, gds_layer_map, via_gen_tbl, timestamp)


if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Convert design json to GDS JSON")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-j", "--json_file_name", type=str, required=True)
  parser.add_argument( "-e", "--exclude_pattern", type=str, default='')

  args = parser.parse_args()

  ofile = open (args.block_name + ".gds.json", 'wt')

  with open( args.json_file_name, "rt") as fp:
    translate( args.block_name, args.exclude_pattern, fp, ofile, timestamp=datetime.now())





