import json
import argparse
from datetime import datetime
import sys
sys.path.append('.')
import gen_gds_json
import gen_lef
import primitive
import pattern_generator

def main( args):
    fin = args.height
    pattern = args.pattern
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gate = 2
    gu = gate + 2*gateDummy
    y_cells = args.Ycells

    if any(args.primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # Dual transistor (current mirror) primitives
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*args.Xcells + 2
        SA, SB, DA, DB, GA, GB = ([] for i in range(6))
        SDG =(SA, GA, DA, SB, GB, DB)
        for k in range(x_cells):
            lS = k*gu+gateDummy
            lG = lS+1
            lD = lS+gate
            if k == (x_cells-2)//2 or k == ((x_cells-2)//2 + 1):
                SA.append(lS)
                GA.append(lG)
                DA.append(lD)
            else:
                SB.append(lS)
                GB.append(lG)
                DB.append(lD)
    elif any(args.primitive.startswith(f'{x}_') for x in ["Switch", "DCL"]):
        # Single transistor primitives
        x_cells = args.Xcells
        SA, SB, DA, DB, GA, GB = ([] for i in range(6))
        SDG =(SA, GA, DA, SB, GB, DB)
        for k in range(x_cells):
            lSA = k*gu+gateDummy
            lGA = lSA+1
            lDA = lSA+gate
            SA.append(lSA)
            GA.append(lGA)
            DA.append(lDA)
    elif any(args.primitive.startswith(f'{x}_') for x in ["CMC", "DP", "SCM"]):
        # Dual transistor primitives
        x_cells = 2*args.Xcells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells%4 != 0 else args.pattern ### CC is not possible; default is interdigitated
        if pattern == 1:
            SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.common_centroid(x_cells, gu, gate, gateDummy)
        else:
            SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.interdigitated(x_cells, gu, gate, gateDummy)

    (S, D, G) = (SA+SB, DA+DB, GA+GB)
    CcM3 = (max(S))//2

    uc = primitive.PrimitiveGenerator( fin, finDummy, gate, gateDummy)

    def gen( pattern, f):
        if 'NMOS' in args.primitive:
            uc.addNMOSArray( x_cells, y_cells, pattern, f)
        else:
            uc.addPMOSArray( x_cells, y_cells, pattern, f)
        return [ t[0] for t in f(0)]

    if args.primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( 0,
                        lambda y: [('S', S, 1, CcM3),
                                   ('D', D, 2, CcM3+1),
                                   ('G', G, 3, CcM3-1)])
 
    elif args.primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( 0,
                        lambda y: [('S', S, 1, CcM3),
                                   ('D', G+D, 2, CcM3+1)])
    
    elif args.primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen( pattern,
                        lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+G if y%2==0 else DB+G, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1)])

    elif args.primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen( pattern,
                        lambda y: [('SA', SA if y%2==0 else SB, 1, CcM3-1),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-2),
                                   ('SB', SB if y%2==0 else SA, 3, CcM3+1),
                                   ('DB', DB if y%2==0 else DA, 4, CcM3+2),
                                   ('G', G, 5, CcM3)])
    
    elif args.primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( 3, 
                        lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+G, 2, CcM3-1),
                                   ('DB', DB, 3, CcM3+1)])

    elif args.primitive in ["CMC_NMOS_S", "CMC_PMOS_S"]:
        cell_pin = gen( pattern,
                        lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1),
                                   ('G', G, 4, CcM3-2)])

    elif args.primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( 3,
                        lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+GA, 2, CcM3-1),
                                   ('DB', DB, 3, CcM3+1),
                                   ('GB', GB, 4, CcM3-2)])

    elif args.primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen( pattern,
                        lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1),
                                   ('GA', GA if y%2==0 else GB, 4, CcM3-2),
                                   ('GB', GB if y%2==0 else GA, 5, CcM3+2)])

    else:
        assert False, "Unrecognized primitive"

    with open(args.block_name + '.json', "wt") as fp:
        uc.writeJSON( fp)

    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())

    return uc

def gen_parser():
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-p", "--primitive", type=str, required=True)
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-u", "--height", type=int, required=False, default=12)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    parser.add_argument( "-s", "--pattern", type=int, required=False, default=1)
    return parser

if __name__ == "__main__":
    main( gen_parser().parse_args())
