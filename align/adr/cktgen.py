
import argparse

from . import techfile

def parse_args( command_line_args=None):
  parser = argparse.ArgumentParser( description="Generates input files for amsr (Analog router)")

  parser.add_argument( "-n", "--block_name", type=str, required=True)
  parser.add_argument( "--route", action='store_true')
  parser.add_argument( "--show_global_routes", action='store_true')
  parser.add_argument( "--show_metal_templates", action='store_true')
  parser.add_argument( "--no_interface", action='store_true')
  parser.add_argument( "--placer_json", type=str, default='')
  parser.add_argument( "--gr_json", type=str, default='')
  parser.add_argument( "-tf", "--technology_file", type=str, default="DR_COLLATERAL/Process.json")
  parser.add_argument( "-s", "--source", type=str, default='')
  parser.add_argument( "--small", action='store_true')
  parser.add_argument( "--nets_to_route", type=str, default='')
  parser.add_argument( "--nets_not_to_route", type=str, default='')
  parser.add_argument( "-tm", "--topmetal", type=str, default='')

  args = parser.parse_args( args=command_line_args)

  with open( args.technology_file) as fp:
    tech = techfile.TechFile( fp)

  return args,tech
