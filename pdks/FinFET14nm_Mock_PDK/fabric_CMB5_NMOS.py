import json
import argparse
import gen_gds_json
import gen_lef
import primitive
from datetime import datetime
                                                           
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-M1", "--M1", type=int, required=True)
    parser.add_argument( "-M2", "--M2", type=int, required=True)
    parser.add_argument( "-M3", "--M3", type=int, required=True)
    parser.add_argument( "-M4", "--M4", type=int, required=True)
    parser.add_argument( "-M5", "--M5", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    fin_u = args.nfin
    x_cells = args.Xcells
    y_cells = args.Ycells
    assert x_cells%2==0, f"total number of transistor must be even in a row"
    assert (args.M1+args.M2+args.M3+args.M4+args.M5) == x_cells*y_cells, f"aspect ratio is not matching with total number of cells"    
    gate = 2
    fin = 2*((fin_u+1)//2)
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gu = gate + 2*gateDummy
     ##### Routing
    SA, SB, DA, DB, GA, GB = ([] for i in range(6))
    for k in range(x_cells//2):
        (p,q) = (gateDummy,gu+gateDummy) if k%2 == 0 else (gu+gateDummy,gateDummy)
        (lSa,lSb) = (2*k*gu+p,2*k*gu+q)
        (lGa,lGb) = (lSa+1,lSb+1)
        (lDa,lDb) = (lSa+gate,lSb+gate)
        SA.append(lSa)
        GA.append(lGa)
        DA.append(lDa)
        SB.append(lSb)
        GB.append(lGb)
        DB.append(lDb)
       
    SDG =(SA, GA, DA, SB, GB, DB)
    (S, D, G) = (SA+SB, DA+DB, GA+GB)
    CcM3 = (min(S)+max(S))//2
    
    uc = primitive.NMOSGenerator( fin_u, fin, finDummy, gate, gateDummy)
   
    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        Routing = [('S', S, 1, CcM3), ('D0', DA+G if y%2==0 else DB+G, 2, CcM3-1), ('D1', DB if y%2==0 else DA, 3, CcM3+1), ('D2', DB if y%2==0 else DA, 4, CcM3+2), ('D3', DA if y%2==0 else DB, 5, CcM3+2), ('D4', DA if y%2==0 else DB, 6, CcM3+3)]

        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

    uc.computeBbox()

    with open(args.block_name + '.json', "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

    cell_pin = ["S", "D0", "D1", "D2", "D3", "D4"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
