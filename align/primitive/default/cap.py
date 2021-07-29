import math

from .canvas import DefaultCanvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class CapGenerator(DefaultCanvas):

    def __init__(self, pdk):
        super().__init__(pdk)

        # TODO: Generalize these !!!
        self.m1n = self.addGen( Wire( 'm1n', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m1Pitch'], width=self.pdk['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], stoppoint=self.pdk['V1']['VencA_L'] +self.pdk['M2']['Width']//2, check=False)))
        self.m2n = self.addGen( Wire( 'm2n', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m2Pitch'], width=self.pdk['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=self.pdk['M1']['Pitch'], stoppoint=self.pdk['V1']['VencA_H'] + self.pdk['M1']['Width']//2, check=False)))

        self.m3n = self.addGen( Wire( 'm3n', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m3Pitch'], width=self.pdk['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=self.pdk['M2']['Pitch'], stoppoint=self.pdk['V2']['VencA_H'] + self.pdk['M2']['Width']//2, check=False)))

        self.Cboundary = self.addGen( Region( 'Cboundary', 'Cboundary', h_grid=self.m2.clg, v_grid=self.m1.clg))

        self.v1_xn = self.addGen( Via( 'v1_xn', 'V1',
                                        h_clg=self.m2n.clg, v_clg=self.m1.clg,
                                        WidthX=self.v1.WidthX, WidthY=self.v1.WidthY,
                                        h_ext=self.v1.h_ext, v_ext=self.v1.v_ext))
        self.v1_nx = self.addGen( Via( 'v1_nx', 'V1',
                                        h_clg=self.m2.clg, v_clg=self.m1n.clg,
                                        WidthX=self.v1.WidthX, WidthY=self.v1.WidthY,
                                        h_ext=self.v1.h_ext, v_ext=self.v1.v_ext))
        self.v2_xn = self.addGen( Via( 'v2_xn', 'V2',
                                        h_clg=self.m2n.clg, v_clg=self.m3.clg,
                                        WidthX=self.v2.WidthX, WidthY=self.v2.WidthY,
                                        h_ext=self.v2.h_ext, v_ext=self.v2.v_ext))
        self.v2_nx = self.addGen( Via( 'v2_nx', 'V2',
                                        h_clg=self.m2.clg, v_clg=self.m3n.clg,
                                        WidthX=self.v2.WidthX, WidthY=self.v2.WidthY,
                                        h_ext=self.v2.h_ext, v_ext=self.v2.v_ext))

    def addCap( self, unit_cap):

        x_length = float((math.sqrt(unit_cap/2))*1000)
        y_length = float((math.sqrt(unit_cap/2))*1000)  

        c_m1_p = self.pdk['Cap']['m1Pitch']
        c_m1_w = self.pdk['Cap']['m1Width']
        c_m2_p = self.pdk['Cap']['m2Pitch']
        c_m2_w = self.pdk['Cap']['m2Width']
        m1_p = self.pdk['M1']['Pitch']
        m2_p = self.pdk['M2']['Pitch']

        logger.debug( f"Pitches {c_m1_p} {c_m2_p} {m1_p} {m2_p}")

        def compute( l, p, w):
            # this is nonsense but if l is a multiple of 2p say 2kp, then 2kp+p-w/(2p) is always k
            return int( 2*round(  (l+p-w)/(2.0*p) ))

        x_number = compute( x_length, c_m1_p, c_m1_w)
        y_number = compute( y_length, c_m2_p, c_m2_w)

        logger.debug( f"Number of wires {x_number} {y_number}")

        def roundup( x, p):
            return (x+p-1)//p

        last_y1_track = roundup( (y_number-1)*c_m2_p, m2_p)
        last_x1_track = roundup( (x_number-1)*c_m1_p, m1_p)

        grid_y0 = 0
        grid_y1 = grid_y0 + last_y1_track

        for i in range(x_number-1):
            grid_x = i
            net = 'PLUS' if i%2 == 1 else 'MINUS'
            self.addWire( self.m1n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))
            self.addWire( self.m3n, net, None, grid_x, (grid_y0, -1), (grid_y1, 1))

            grid_y = ((i+1)%2)*grid_y1

            self.addVia( self.v1_nx, net, None, grid_x, grid_y)
            self.addVia( self.v2_nx, net, None, grid_x, grid_y)

        pin = 'PLUS'
        # Don't port m1 per Yaguang instructions
        self.addWire( self.m1, 'PLUS', None, last_x1_track, (grid_y0, -1), (grid_y1, 1))
        # don't port m3 (or port one or the other)
        self.addWire( self.m3, 'PLUS', None, last_x1_track, (grid_y0, -1), (grid_y1, 1))

        grid_x0 = 0
        grid_x1 = grid_x0 + last_x1_track
        netType = 'drawing'
        for i in range(y_number-1):
            grid_x = ((i+1)%2)*grid_x1
            net = 'PLUS' if i%2 == 0 else 'MINUS'
            self.addVia( self.v1_xn, net, None, grid_x, i)
            self.addVia( self.v2_xn, net, None, grid_x, i)
            pin = 'PLUS' if i == 0 else None
            if i == 0:
                netType = 'pin'
            else:
                netType = 'drawing'
            self.addWire( self.m2n, net, pin, i, (grid_x0, -1), (grid_x1, 1), netType = netType)

        pin = 'MINUS'
        self.addWire( self.m2, 'MINUS', pin, last_y1_track, (grid_x0, -1), (grid_x1, 1), netType = 'pin')

        self.addRegion( self.boundary, 'Boundary', None,
                        0, 0,
                        last_x1_track,
                        last_y1_track)

        #self.addRegion( self.Cboundary, 'Cboundary', None,
        #                    -1, -1,
        #                    last_x_track  + x * grid_cell_x_pitch + 1 + p,
        #                    last_y1_track + y * grid_cell_y_pitch + 1)

        logger.debug( f"Computed Boundary: {self.terminals[-1]} {self.terminals[-1]['rect'][2]} {self.terminals[-1]['rect'][2]%80}")
