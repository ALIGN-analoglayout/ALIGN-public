import json
import math
import argparse
import gen_gds_json
import gen_lef
from datetime import datetime
from cell_fabric import Canvas, Pdk, Wire, Region, Via
from cell_fabric import EnclosureGrid
from cell_fabric import ColoredCenterLineGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / '../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json').resolve()

class CanvasCap(Canvas):

    def __init__( self, x_length, y_length):
        super().__init__()
        p = Pdk().load(pdkfile)
        
        self.x_number = int(2*round(((x_length+p['Cap']['m1Pitch']-p['Cap']['m1Width'])/(2.0*p['Cap']['m1Pitch']))))
        self.y_number = int(2 *round(((y_length+p['Cap']['m2Pitch']-p['Cap']['m2Width'])/(2.0*p['Cap']['m2Pitch']))))
       
        self.last_y1_track = ((self.y_number-1)*p['Cap']['m2Pitch']+p['M2']['Pitch']-1)//p['M2']['Pitch']
        self.last_x_track = self.x_number - 1

        self.m1 = self.addGen( Wire( 'm1', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m1Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['V1']['VencA_L'] +p['Cap']['m2Width']//2, check=True)))

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
        self.v2 = self.addGen( Via( 'v2', 'V1', h_clg=self.m2.clg, v_clg=self.m3.clg))


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

        #print( "last_x_track (m1Pitches)", last_x_track, "last_y1_track (m2Pitch_standards)", last_y1_track)

        #gcd = math.gcd( self.m2Pitch_narrow, self.m2Pitch_standard)
        #print( "GCD,LCM,(LCM in m2Pitch_narrowes),(LCM in m2Pitch_standards) of m2Pitch_narrow (minimum) and m2Pitch_standard (devices)", gcd, self.m2Pitch_narrow, self.m2Pitch_standard, (self.m2Pitch_narrow*self.m2Pitch_standard)//gcd, self.m2Pitch_standard//gcd, self.m2Pitch_narrow//gcd)

        grid_y0 = y*grid_cell_y_pitch
        grid_y1 = grid_y0 + self.last_y1_track

        for i in range(self.x_number):
            grid_x = i + x*grid_cell_x_pitch
            
            net = 'PLUS' if i%2 == 1 else 'MINUS'

            self.addWire( self.m1, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.m3, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))

            grid_y = ((i+1)%2)*self.last_y1_track + grid_y0

            self.addVia( self.v1, net, None, grid_x, grid_y)
            self.addVia( self.v2, net, None, grid_x, grid_y)

#
# Build the narrow m2 pitch grid starting at grid_cell_y_pitch*y in standard m2 pitch grids (m2.clg)
#
        m2n = Wire( self.m2n.nm, self.m2n.layer, self.m2n.direction,
                    clg=self.m2n.clg.copyShift( self.m2.clg.value( grid_cell_y_pitch*y)[0]),
                    spg=self.m2n.spg)

        v1n = Via( 'v1', 'V1', h_clg=m2n.clg, v_clg=self.m1.clg)
        v2n = Via( 'v2', 'V2', h_clg=m2n.clg, v_clg=self.m3.clg)

        grid_x0 = x*grid_cell_x_pitch
        grid_x1 = grid_x0 + self.last_x_track

        for i in range(self.y_number-1):
            grid_x = x*grid_cell_x_pitch + ((i+1)%2)*(self.x_number-1)
            
            pin = 'PLUS' if y == 0 and x == 0 and i == 0 else None

            net = 'PLUS' if i%2 == 0 else 'MINUS'

            self.addVia( v1n, net, None, grid_x, i)
            self.addVia( v2n, net, None, grid_x, i)

            self.addWire( m2n, net, pin, i, (grid_x0, -1), (grid_x1, 1))

        grid_y = self.last_y1_track + grid_cell_y_pitch*y

        pin = 'MINUS'
        self.addWire( self.m2, 'MINUS', pin, grid_y, (grid_x0, -1), (grid_x1, 1))

        if x == x_cells-1 and y == y_cells-1:            
            self.addRegion( self.boundary, 'boundary', None,
                            -1, -1,
                            self.last_x_track  + x*grid_cell_x_pitch + 1,
                            self.last_y1_track + y*grid_cell_y_pitch + 1)
                                                                          
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--unit_cap", type=float, required=True)
    #parser.add_argument( "-X", "--Xcells", type=int, required=True)
    #parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    
    #x_cells = args.Xcells
    #y_cells = args.Ycells
    unit_cap = args.unit_cap
    x_cells = 1
    y_cells = 1
    x_length = float((math.sqrt(unit_cap/2))*1000)
    y_length = float((math.sqrt(unit_cap/2))*1000)  

    uc = UnitCell(x_length, y_length)

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
