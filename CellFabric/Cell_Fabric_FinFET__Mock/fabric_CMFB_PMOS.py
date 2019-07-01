import json
import argparse
import gen_gds_json
import gen_lef
import fabric_PMOS
from datetime import datetime
                                                           
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    fin_u = args.nfin
    x_cells = 2*args.Xcells
    x_cells = x_cells + 2
    y_cells = 1
    gate = 2
    fin = 2*((fin_u+1)//2)
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gu = gate + 2*gateDummy
     ##### Routing
    SA, SB, DA, DB, GA, GB = ([] for i in range(6))
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
       
    SDG =(SA, GA, DA, SB, GB, DB)
    (S, D, G) = (SA+SB, DA+DB, GA+GB)
    CcM3 = (min(S)+max(S))//2
    Routing = [('S', S, 1, CcM3), ('DA', DA+GA, 2, CcM3-1), ('DB', DB, 3, CcM3+1), ('GB', GB, 4, CcM3-2)]
    uc = fabric_PMOS.UnitCell( fin_u, fin, finDummy, gate, gateDummy)
   
    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

    uc.computeBbox()

    with open(args.block_name + '.json', "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

    cell_pin = ["S", "DA", "DB","GB"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
