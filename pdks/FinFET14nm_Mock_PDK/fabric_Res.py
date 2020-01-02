import json
import argparse
import gen_gds_json
import gen_lef
from datetime import datetime
from align.cell_fabric import Via, Region, Canvas, Wire, Pdk
from align.cell_fabric import EnclosureGrid
from align.cell_fabric import ColoredCenterLineGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / 'layers.json').resolve()

class CanvasCap(Canvas):

    def __init__( self, x_number, y_length):
        super().__init__()
        p = Pdk().load(pdkfile)
        
        ga = 2 if x_number == 1 else 1 ## when number of wires is 2 then large spacing req. so contact can be placed without a DRC error 
        self.x_length = (x_number - 1) *ga*p['Cap']['m1Pitch']

        self.y_number = int(2 *round(((y_length+p['Cap']['m2Pitch']-p['Cap']['m2Width'])/(2.0*p['Cap']['m2Pitch']))))
       
        self.last_y1_track = ((self.y_number-1)*p['Cap']['m2Pitch']+p['M2']['Pitch']-1)//p['M2']['Pitch']
        self.last_x_track = x_number - 1

        self.m1 = self.addGen( Wire( 'm1', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m1Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['V1']['VencA_L'] +p['Cap']['m2Width']//2, check=True)))
         
        self.m1h = self.addGen( Wire( 'm1h', 'M1', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['M2']['Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['Cap']['m1Width']//2, check=False)))

        self.m2 = self.addGen( Wire( 'm2', 'M2', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['M2']['Pitch'], width=p['Cap']['m2Width']),
                                     spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['V1']['VencA_H'] + p['Cap']['m1Width']//2, check=False)))

        self.m2n = self.addGen( Wire( 'm2n', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m2Pitch'], width=p['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['V1']['VencA_H'] + p['Cap']['m1Width']//2)))

        self.m3 = self.addGen( Wire( 'm3', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m3Pitch'], width=p['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=p['M2']['Pitch'], stoppoint=p['V2']['VencA_H'] + p['Cap']['m2Width']//2, check=True)))

        self.boundary = self.addGen( Region( 'boundary', 'boundary', h_grid=self.m2.clg, v_grid=self.m1.clg))
        self.v1 = self.addGen( Via( 'v1', 'V1', h_clg=self.m2.clg, v_clg=self.m1.clg))
        self.v2 = self.addGen( Via( 'v2', 'V2', h_clg=self.m2.clg, v_clg=self.m3.clg))


class UnitCell(CanvasCap):

    def unit( self, x, y, x_cells, y_cells):
        m2factor = 2 ### number of m2-tracks (m2factor-1)in between two unitcells in y-direction
        m1factor = 3
                
        if (self.y_number-1) % 2 != self.last_y1_track % 2:
            self.last_y1_track += 1 # so the last color is compatible with the external view of the cell

        if self.last_y1_track % 2 == 1:
            m2factor += 1 # so colors match in arrayed blocks

        grid_cell_x_pitch = m1factor + self.last_x_track
        grid_cell_y_pitch = m2factor + self.last_y1_track

        grid_y0 = y*grid_cell_y_pitch
        grid_y1 = grid_y0 + self.last_y1_track

        for i in range(x_number):
            (k, p) = (2*i, 1) if x_number==2 else (i, 0)
            grid_x = k + x*grid_cell_x_pitch
            
            self.addWire( self.m1, 'M1', None, grid_x, (grid_y0, -1), (grid_y1, 1))
            if i < x_number-1:
                grid_yh = ((i+1)%2)*self.last_y1_track
                self.addWire( self.m1h, 'M1', None, grid_yh, (i, -1), (i+p+1, 1))
            
           
#
# Build the narrow m2 pitch grid starting at grid_cell_y_pitch*y in standard m2 pitch grids (m2.clg)
#
        m2n = Wire( self.m2n.nm, self.m2n.layer, self.m2n.direction,
                    clg=self.m2n.clg.copyShift( self.m2.clg.value( grid_cell_y_pitch*y)[0]),
                    spg=self.m2n.spg)

        #v1n = Via( 'v1', 'via1', h_clg=m2n.clg, v_clg=self.m1.clg)
        #v2n = Via( 'v2', 'via2', h_clg=m2n.clg, v_clg=self.m3.clg)

        grid_x0 = x*grid_cell_x_pitch
        grid_x1 = grid_x0 + self.last_x_track
        grid_y = (x_number%2)*self.last_y1_track
        
        pin = 'PLUS'
        self.addWire( m2n, 'PLUS', pin, 0, (0, -1), (0, 1))
        self.addVia( self.v1, 'V1', None, 0, 0)
        pin = 'MINUS'
        self.addWire( self.m2, 'MINUS', pin, grid_y, (grid_x1+p, -1), (grid_x1+p, 1))
        self.addVia( self.v1, 'V1', None, grid_x1+p, grid_y)

        if x == x_cells-1 and y == y_cells-1:            
            self.addRegion( self.boundary, 'boundary', None,
                            -1, -1,
                            self.last_x_track  + x*grid_cell_x_pitch + 1 + p,
                            self.last_y1_track + y*grid_cell_y_pitch + 1)
                                                                          
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--height", type=int, required=True)
    parser.add_argument( "-r", "--res", type=float, required=True)
    #parser.add_argument( "-X", "--Xcells", type=int, required=True)
    #parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    
    #x_cells = args.Xcells
    #y_cells = args.Ycells
    input_resistance = args.res
    y_length = 420*args.height
    x_cells = 1
    y_cells = 1 
    res_per_length = 67
    x_number = int(round(((1000*input_resistance)/(res_per_length*y_length))))    
    uc = UnitCell(x_number, y_length)

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y, x_cells, y_cells)

    uc.computeBbox()

    with open(args.block_name + '.json', "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
    cell_pin = ["PLUS", "MINUS"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    with open( args.block_name + ".json", "rt") as fp0, \
         open( args.block_name + ".gds.json", 'wt') as fp1:
        gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
