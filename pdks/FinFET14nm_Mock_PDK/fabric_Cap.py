import math
import argparse
import gen_gds_json
import gen_lef
import pathlib

from datetime import datetime
from align.cell_fabric import DefaultCanvas, Pdk, Wire, Region, Via
from align.cell_fabric import EnclosureGrid
from align.cell_fabric import ColoredCenterLineGrid

pdkfile = (pathlib.Path(__file__).parent / 'layers.json').resolve()

class CanvasCap(DefaultCanvas):

    def __init__( self, x_length, y_length):
        p = Pdk().load(pdkfile)
        super().__init__(p)

        c_m1_p = p['Cap']['m1Pitch']
        c_m1_w = p['Cap']['m1Width']
        c_m2_p = p['Cap']['m2Pitch']
        c_m2_w = p['Cap']['m2Width']
        m1_p = p['M1']['Pitch']
        m2_p = p['M2']['Pitch']

        print( f"Pitches {c_m1_p} {c_m2_p} {m1_p} {m2_p}")

        def compute( l, p, w):
            # this is nonsense but if l is a multiple of 2p say 2kp, then 2kp+p-w/(2p) is always k
            return int( 2*round(  (l+p-w)/(2.0*p) ))

        self.x_number = compute( x_length, c_m1_p, c_m1_w)
        self.y_number = compute( y_length, c_m2_p, c_m2_w)

        print( f"Number of wires {self.x_number} {self.y_number}")

        def roundup( x, p):
            return (x+p-1)//p

        self.last_y1_track = roundup( (self.y_number-1)*c_m2_p, m2_p)
        self.last_x1_track = roundup( (self.x_number-1)*c_m1_p, m1_p)

        print( "last_x1_track (m1Pitches_standards)", self.last_x1_track, "last_y1_track (m2Pitch_standards)", self.last_y1_track)

        self.m1n = self.addGen( Wire( 'm1n', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m1Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['V1']['VencA_L'] +p['M2']['Width']//2, check=False)))
        self.m2n = self.addGen( Wire( 'm2n', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m2Pitch'], width=p['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=p['M1']['Pitch'], stoppoint=p['V1']['VencA_H'] + p['M1']['Width']//2, check=False)))

        self.m3n = self.addGen( Wire( 'm3n', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m3Pitch'], width=p['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=p['M2']['Pitch'], stoppoint=p['V2']['VencA_H'] + p['M2']['Width']//2, check=False)))

        self.boundary = self.addGen( Region( 'boundary', 'Boundary', h_grid=self.m2.clg, v_grid=self.m1.clg))

        self.v1_xn = self.addGen( Via( 'v1_xn', 'V1', h_clg=self.m2n.clg, v_clg=self.m1.clg))
        self.v1_nx = self.addGen( Via( 'v1_nx', 'V1', h_clg=self.m2.clg, v_clg=self.m1n.clg))
        self.v2_xn = self.addGen( Via( 'v2_xn', 'V2', h_clg=self.m2n.clg, v_clg=self.m3.clg))
        self.v2_nx = self.addGen( Via( 'v2_nx', 'V2', h_clg=self.m2.clg, v_clg=self.m3n.clg))


class UnitCell(CanvasCap):

    def unit( self):

        grid_y0 = 0
        grid_y1 = grid_y0 + self.last_y1_track

        for i in range(self.x_number-1):
            grid_x = i
            net = 'PLUS' if i%2 == 1 else 'MINUS'
            self.addWire( self.m1n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.m3n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))

            grid_y = ((i+1)%2)*grid_y1

            self.addVia( self.v1_nx, net, None, grid_x, grid_y)
            self.addVia( self.v2_nx, net, None, grid_x, grid_y)

        pin = 'PLUS'
        # Don't port m1 per Yaguang instructions
        self.addWire( self.m1, 'PLUS', None, self.last_x1_track, (grid_y0, -1), (grid_y1, 1))
        # don't port m3 (or port one or the other)
        self.addWire( self.m3, 'PLUS', None, self.last_x1_track, (grid_y0, -1), (grid_y1, 1))

        grid_x0 = 0
        grid_x1 = grid_x0 + self.last_x1_track

        for i in range(self.y_number-1):
            grid_x = ((i+1)%2)*grid_x1
            net = 'PLUS' if i%2 == 0 else 'MINUS'
            self.addVia( self.v1_xn, net, None, grid_x, i)
            self.addVia( self.v2_xn, net, None, grid_x, i)
            pin = 'PLUS' if i == 0 else None
            self.addWire( self.m2n, net, pin, i, (grid_x0, -1), (grid_x1, 1))

        pin = 'MINUS'
        self.addWire( self.m2, 'MINUS', pin, self.last_y1_track, (grid_x0, -1), (grid_x1, 1))


        self.addRegion( self.boundary, 'Boundary', None,
                        0, 0,
                        self.last_x1_track,
                        self.last_y1_track)
        
        print( "Computed Boundary:", self.terminals[-1], self.terminals[-1]['rect'][2], self.terminals[-1]['rect'][2]%80)

                                                                          
def gen_parser():
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--unit_cap", type=float, default=None)
    parser.add_argument( "--x_length", type=int, default=None)
    parser.add_argument( "--y_length", type=int, default=None)
    parser.add_argument( "-q", "--pinSwitch", type=int, required=False, default=0)
    parser.add_argument( "-d", "--pdkdir", type=pathlib.Path, required=False, default=pathlib.Path(__file__).resolve().parent)
    parser.add_argument( "-o", "--outputdir", type=pathlib.Path, required=False, default=pathlib.Path.cwd().resolve())
    return parser


    
def main( args):    
    if args.unit_cap is None:
        assert args.x_length is not None and args.y_length is not None
        x_length = args.x_length * 64
        y_length = args.y_length * 64
        print( "No unit_cap", x_length, y_length)
    else:
        unit_cap = args.unit_cap
        x_length = float((math.sqrt(unit_cap/2))*1000)
        y_length = float((math.sqrt(unit_cap/2))*1000)  
        print( "With unit_cap", x_length, y_length)

    uc = UnitCell(x_length, y_length)

    uc.unit()

    uc.setBboxFromBoundary()

    print( "bbox", uc.bbox)

    with open(args.outputdir / (args.block_name + '.json'), "wt") as fp:
        uc.writeJSON( fp, draw_grid=False)

    cell_pin = ["PLUS", "MINUS"]
    gen_lef.json_lef(args.outputdir / (args.block_name + '.json'),args.block_name,cell_pin)
    with open( args.outputdir / (args.block_name + ".json"), "rt") as fp0, \
         open( args.outputdir / (args.block_name + ".gds.json"), 'wt') as fp1:
        #gen_gds_json.translate(args.block_name, '', fp0, fp1, datetime.now())
        gen_gds_json.translate(args.block_name, '', args.pinSwitch, fp0, fp1, datetime.now()) 

    return uc

if __name__ == "__main__":
    main( gen_parser().parse_args())
