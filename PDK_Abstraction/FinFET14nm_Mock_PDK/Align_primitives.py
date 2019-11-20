import argparse
from datetime import datetime
import sys
import pathlib
import logging

sys.path.append(pathlib.Path(__file__).parent.resolve())
import gen_gds_json
import gen_lef
import primitive
import json

def get_xcells_pattern( args):
    pattern = args.pattern
    if any(args.primitive.startswith(f'{x}_') for x in ["Switch", "DCL"]):
        # Single transistor primitives
        x_cells = args.Xcells
    elif any(args.primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # Dual transistor (current mirror) primitives
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*args.Xcells + 2
    elif any(args.primitive.startswith(f'{x}_') for x in ["SCM", "CMC", "DP"]):
        # Dual transistor primitives
        x_cells = 2*args.Xcells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells%4 != 0 else args.pattern ### CC is not possible; default is interdigitated
    return x_cells, pattern

def get_parameters(args):
    parameters = args.params
    if 'model' not in parameters:
        parameters['model'] = 'NMOS' if 'NMOS' in args.primitive else 'PMOS'
    parameters['nfin'] = args.nfin
    return parameters

def main( args):

    logging.basicConfig(level=logging.getLevelName(args.logLevel))

    fin = args.height
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gate = 2
    y_cells = args.Ycells

    x_cells, pattern = get_xcells_pattern(args)
    parameters = get_parameters(args)

    uc = primitive.PrimitiveGenerator( fin, finDummy, gate, gateDummy)

    def gen( pattern, routing):
        if 'NMOS' in args.primitive:
            uc.addNMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        else:
            uc.addPMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        return routing.keys()

    if args.primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G')]})

    elif args.primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'G'), ('M1', 'D')]})

    elif args.primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif args.primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G')],
                                 'DB': [('M2', 'D')],
                                 'GB': [('M2', 'G')]})

    elif args.primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif args.primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'DA': [('M1', 'D')],
                                 'SB': [('M2', 'S')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})


    elif args.primitive in ["CMC_NMOS_S", "CMC_PMOS_S"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})

    elif args.primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'GA': [('M1', 'G')],
                                 'GB': [('M2', 'G')]})

    else:
        assert False, f"Unrecognized primitive {args.primitive}"

    with open(args.block_name + '.json', "wt") as fp:
        uc.writeJSON( fp)

    gen_lef.json_lef(args.block_name + '.json', args.block_name, cell_pin)
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
    parser.add_argument( "--model", type=str, required=False, default=None)
    parser.add_argument( "--params", type=json.loads, required=False, default='{}')
    parser.add_argument( "-l", "--log", dest="logLevel", choices=['DEBUG','INFO','WARNING','ERROR','CRITICAL'], default='ERROR', help="Set the logging level (default: %(default)s)")
    return parser

if __name__ == "__main__":
    main( gen_parser().parse_args())
