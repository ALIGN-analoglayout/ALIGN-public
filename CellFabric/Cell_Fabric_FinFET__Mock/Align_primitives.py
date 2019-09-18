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
    x_cells = 2*args.Xcells
    pattern = 2 if x_cells%4 != 0 else args.pattern ### CC is not possible; default is interdigitated

    if args.primitive in ["Switch_NMOS", "Switch_PMOS", "DCL_NMOS", "DCL_PMOS"]:
        x_cells = args.Xcells
    elif args.primitive in ["CM_NMOS", "CM_PMOS", "CMFB_NMOS", "CMFB_PMOS"]:
        x_cells = x_cells + 2
    else:
        pass

    if pattern == 1:  
        SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.common_centroid(x_cells, gu, gate, gateDummy)
    else:
        SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.interdigitated(x_cells, gu, gate, gateDummy)

    ### For Current Mirror; need to be updated later ###    
    if args.primitive in ["CM_NMOS", "CM_PMOS", "CMFB_NMOS", "CMFB_PMOS"]:
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
    ### End ###

    if args.primitive in ["Switch_NMOS", "Switch_PMOS", "DCL_NMOS", "DCL_PMOS"]:
        SA, SB, DA, DB, GA, GB = ([] for i in range(6))
        SDG =(SA, GA, DA, SB, GB, DB)
        for k in range(x_cells):
            lSA = k*gu+gateDummy
            lGA = lSA+1
            lDA = lSA+gate
            SA.append(lSA)
            GA.append(lGA)
            DA.append(lDA)

    (S, D, G) = (SA+SB, DA+DB, GA+GB)
    CcM3 = (min(S)+max(S))//2

    uc = primitive.PrimitiveGenerator( fin, finDummy, gate, gateDummy)

    def gen( f):
        if args.primitive in ["Switch_NMOS", "DCL_NMOS", "DP_NMOS", "CM_NMOS", "CMC_NMOS", "SCM_NMOS", "CMC_NMOS_S"]:
            uc.addNMOSArray( x_cells, y_cells, f)
        else:
            uc.addPMOSArray( x_cells, y_cells, f)
        return [ t[0] for t in f(0)]

    if args.primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('D', D, 2, CcM3+1),
                                   ('G', G, 3, CcM3-1)])
 
    elif args.primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('D', G+D, 2, CcM3+1)])
    
    elif args.primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+G if y%2==0 else DB+G, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1)])

    elif args.primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen( lambda y: [('SA', SA if y%2==0 else SB, 1, CcM3-1),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-2),
                                   ('SB', SB if y%2==0 else SA, 3, CcM3+1),
                                   ('DB', DB if y%2==0 else DA, 4, CcM3+2),
                                   ('G', G, 5, CcM3)])
    
    elif args.primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+G, 2, CcM3-1),
                                   ('DB', DB, 3, CcM3+1)])

    elif args.primitive in ["CMC_NMOS_S", "CMC_PMOS_S"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1),
                                   ('G', G, 4, CcM3-2)])

    elif args.primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA+GA, 2, CcM3-1),
                                   ('DB', DB, 3, CcM3+1),
                                   ('GB', GB, 4, CcM3-2)])

    elif args.primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen( lambda y: [('S', S, 1, CcM3),
                                   ('DA', DA if y%2==0 else DB, 2, CcM3-1),
                                   ('DB', DB if y%2==0 else DA, 3, CcM3+1),
                                   ('GA', GA if y%2==0 else GB, 4, CcM3-2),
                                   ('GB', GB if y%2==0 else GA, 5, CcM3+2)])

    else:
        assert False

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
