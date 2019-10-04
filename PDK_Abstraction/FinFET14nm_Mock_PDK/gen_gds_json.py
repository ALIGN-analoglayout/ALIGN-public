#!/usr/bin/env python
import argparse
from datetime import datetime
from cell_fabric import gen_gds_json, pdk

from pathlib import Path
pdkfile = (Path(__file__).parent / '../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json').resolve()

def translate( macro_name, exclude_pattern, fp, ofile, timestamp=None, p=None):
  if p is None:
    p = pdk.Pdk().load(pdkfile)
  gds_layer_map = p.get_gds_map()

  gds_layer_map.update( {
          "nwell" : 1,
          "fin" : 2,
          "poly" : 3,
          "GCUT" : 4,
          "active" : 5,
          "SDT" : 6,
          "nselect" : 7,
          "pselect" : 8,
          "SLVT" : 9,
          "LVT" : 10,
          "LISD": 98,
          "polycon" : 11,
          "pc": 99,
          "cellarea" : 100,
          "BOUNDARY" : 100,
          "boundary" : 100,
          "bbox" : 100,
          "diearea" : 100
      } )

  via_gen_tbl = {
      "V2": (
          "M3_M2_CDNS_543864435520",
          {
          "V2": [-640,-640,640,640],
          "M2": [-1440,-640,1440,640],
          "M3": [-640,-1440,640,1440]
          }
      ),
      "V1": (
          "M2_M1_CDNS_543864435521",
          {
          "V1": [-640,-640,640,640],
          "M1": [-640,-1440,640,1440],
          "M2": [-1440,-640,1440,640]
          }
      )
  }

  return gen_gds_json.translate(macro_name, exclude_pattern, fp, ofile, gds_layer_map, via_gen_tbl, timestamp)


if __name__ == "__main__":

  parser = argparse.ArgumentParser( description="Convert design json to GDS JSON")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "-j", "--json_file_name", type=str, required=True)
  parser.add_argument( "-e", "--exclude_pattern", type=str, default='')

  args = parser.parse_args()

  ofile = open (args.block_name + ".gds.json", 'wt')

  with open( args.json_file_name, "rt") as fp:
    translate( args.block_name, args.exclude_pattern, fp, ofile, timestamp=datetime.now())





