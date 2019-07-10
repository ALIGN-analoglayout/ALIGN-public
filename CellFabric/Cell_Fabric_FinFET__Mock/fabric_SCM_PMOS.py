import json
import argparse
import gen_gds_json
import gen_lef
import fabric_PMOS
import pattern_generator
from datetime import datetime
                                                           
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-u", "--height", type=int, required=False, default=12)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    parser.add_argument( "-p", "--pattern", type=int, required=False, default=1)
    args = parser.parse_args()
    fin_u = 2*((args.nfin+1)//2)
    fin = args.height
    x_cells = 2*args.Xcells
    y_cells = args.Ycells
    pattern = args.pattern
    gate = 2
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gu = gate + 2*gateDummy
     ##### Routing

    pattern = 2 if x_cells%4 != 0 else args.pattern ### CC is not possible; default is interdigitated
       
    if pattern == 1:  
        SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.common_centroid(x_cells, gu, gate, gateDummy)
    else:
        SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.interdigitated(x_cells, gu, gate, gateDummy)

    (S, D, G) = (SA+SB, DA+DB, GA+GB)
    CcM3 = (min(S)+max(S))//2

    uc = fabric_PMOS.UnitCell( fin_u, fin, finDummy, gate, gateDummy)
   
    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        Routing = [('S', S, 1, CcM3), ('DA', DA+G if y%2==0 else DB+G, 2, CcM3-1), ('DB', DB if y%2==0 else DA, 3, CcM3+1)]
        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

    uc.computeBbox()

    with open(args.block_name + '.json', "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

    cell_pin = ["S", "DA", "DB"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
