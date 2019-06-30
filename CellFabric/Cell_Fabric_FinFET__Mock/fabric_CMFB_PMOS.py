import json
import argparse
import gen_gds_json
import gen_lef
import itertools
from datetime import datetime

from cell_fabric import Via, Region, Canvas, Wire, Pdk
from primitive import CanvasNMOS
from cell_fabric import CenterLineGrid, UncoloredCenterLineGrid, ColoredCenterLineGrid
from cell_fabric import Grid, EnclosureGrid, SingleGrid, CenteredGrid
        
class UnitCell(CanvasNMOS):

    def __init__( self, fin_u, fin, finDummy, gate, gateDummy):
        super().__init__(fin_u, fin, finDummy, gate, gateDummy)


    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy):

        #####   This part generats locations of S/D/G   #####
        gu = self.gatesPerUnitCell
        fin = self.finsPerUnitCell
        h = self.m2PerUnitCell
                       
        self.addWire( self.active, 'active', None, y, (x,1), (x+1,-1)) 
        self.addWire( self.RVT,    'RVT',    None, y, (x, 1), (x+1, -1)) 
 
        for i in range(fin):
            self.addWire( self.fin, 'fin', None, fin*y+i, x, x+1)

        #####   Gate Placement   #####                       
        for i in range(gu):        
            self.addWire( self.pl, 'g', None, gu*x+i,   (y,0), (y,1))

        #####   Pselect/nwell Placement   #####
        if x == x_cells -1 and y == y_cells -1:      
            self.addRegion( self.pselect, 'ps', None, (0, -1), -1, ((1+x)*gu, -1), (y+1)*fin+1)                                                
            self.addRegion( self.nwell, 'nw', None, (0, -1), -1, ((1+x)*gu, -1), (y+1)*fin+1)    
 
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

        (S,D,G) = (SA+SB,DA+DB,GA+GB)
        CcM3 = (min(S)+max(S))//2
        Routing = [('S', S, 1, CcM3), ('DA', DA+GA, 2, CcM3-1), ('DB', DB, 3, CcM3+1), ('GB', GB, 4, CcM3-2)]
        if x_cells-1==x:
            grid_y0 = y*h + finDummy//2-1
            grid_y1 = grid_y0+(fin_u+2)//2
            for i in G:
                self.addWire( self.m1, '_', None, i, (grid_y0, -1), (grid_y1, 1))
            for i in S+D:
                SD = 'S' if i in S else 'D'
                self.addWire( self.m1, SD, None, i, (grid_y0, -1), (grid_y1, 1)) 
                for j in range(1,self.v0.h_clg.n):
                    self.addVia( self.v0, 'v0', None, i, (y, j))

            #pin = 'VDD' if y%2==0 else 'GND'    
            #self.addWire( self.m2, pin, pin, h*(y+1), (0, 1), (x_cells*gu, -1))
            #self.addWire( self.m2, 'GND', 'GND', 0, (0, 1), (x_cells*gu, -1))                   
            for (pin, contact, track, m3route) in Routing:
                self.addWire( self.m2,'_', pin, y*h+track, (min(contact), -1), (max(contact), 1))
                if y_cells > 1:
                   self.addWire( self.m3,'_', None, m3route, (track, -1), (y*h+track, 1))
                   self.addVia( self.v2,'_', None, m3route, track)
                   self.addVia( self.v2,'_', None, m3route, y*h+track)

                for i in contact:
                    self.addVia( self.v1, '_', None, i, y*h+track) 
                                                                                                                                               
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

    uc = UnitCell( fin_u, fin, finDummy, gate, gateDummy)

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy)

    uc.computeBbox()

    with open(args.block_name + '.json', "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')

    cell_pin = ["S", "GB", "DA", "DB"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
