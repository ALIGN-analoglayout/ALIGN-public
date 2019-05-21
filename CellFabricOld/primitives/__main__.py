
import json
from .fabric_gf import *

def gen_nunit():
    c = Canvas()

    for (x,y) in ( (x,y) for x in range(2) for y in range(1)):
        c.nunit( x, y)

    c.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : c.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : c.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

def gen_cunit():
    c = Canvas()

    for (x,y) in ( (x,y) for x in range(16) for y in range(4)):
        c.cunit( x, y)

    c.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : c.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : c.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

import argparse

def main():
    parser = argparse.ArgumentParser( description="Build test device and cap fabrics")
    parser.add_argument( "-n", "--block_name", type=str, required=True)
    args = parser.parse_args()

    if args.block_name == "nunit":
        gen_nunit()
    elif args.block_name == "cunit":
        gen_cunit()

if __name__ == "__main__":
    main()
