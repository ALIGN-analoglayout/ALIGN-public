from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric.generators import *
from align.cell_fabric.grid import *

import logging
logger = logging.getLogger(__name__)

class ResGenerator(DefaultCanvas):

    def __init__(self, pdk, fin, finDummy):
        super().__init__(pdk)
        self.finsPerUnitCell = fin + 2*finDummy
        # TODO: Generalize these
        self.m1res = self.addGen( Wire( 'm1res', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m1Pitch'], width=self.pdk['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=self.pdk['M2']['Pitch'], stoppoint=self.pdk['V1']['VencA_L'] +self.pdk['Cap']['m2Width']//2, check=True)))

        self.m1res2 = self.addGen( Wire( 'm1res2', 'M1', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['M2']['Pitch'], width=self.pdk['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=self.pdk['Cap']['m1Pitch'], stoppoint=self.pdk['Cap']['m1Width']//2, check=False)))

        self.m2res = self.addGen( Wire( 'm2res', 'M2', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['M2']['Pitch'], width=self.pdk['Cap']['m2Width']),
                                     spg=EnclosureGrid( pitch=self.pdk['Cap']['m1Pitch'], stoppoint=self.pdk['V1']['VencA_H'] + self.pdk['Cap']['m1Width']//2, check=False)))

        self.m2res2 = self.addGen( Wire( 'm2res2', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m2Pitch'], width=self.pdk['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=self.pdk['Cap']['m1Pitch'], stoppoint=self.pdk['V1']['VencA_H'] + self.pdk['Cap']['m1Width']//2)))

        self.m3res = self.addGen( Wire( 'm3res', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.pdk['Cap']['m3Pitch'], width=self.pdk['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=self.pdk['M2']['Pitch'], stoppoint=self.pdk['V2']['VencA_H'] + self.pdk['Cap']['m2Width']//2, check=True)))

        self.v1res = self.addGen( Via( 'v1res', 'V1',
                                        h_clg=self.m2res.clg, v_clg=self.m1res.clg,
                                        WidthX=self.v1.WidthX, WidthY=self.v1.WidthY,
                                        h_ext=self.v1.h_ext, v_ext=self.v1.v_ext))
        self.v2res = self.addGen( Via( 'v2res', 'V2', h_clg=self.m2res.clg, v_clg=self.m3res.clg,
                                        WidthX=self.v2.WidthX, WidthY=self.v2.WidthY,
                                        h_ext=self.v2.h_ext, v_ext=self.v2.v_ext))

        self.Rboundary = self.addGen( Region( 'Rboundary', 'Rboundary', h_grid=self.m2.clg, v_grid=self.m1.clg))

    def addResArray(self, x_cells, y_cells, height, unit_res):

        for x in range(x_cells):
            for y in range(y_cells):
                self._addRes(x, y, height, unit_res, (x == x_cells-1) and (y == y_cells-1))

    def _addRes( self, x, y, height, unit_res, draw_boundary=True):

        y_length = self.finsPerUnitCell * self.pdk['Fin']['Pitch'] * height
        assert y_length != 0, (self.finsPerUnitCell, self.pdk['Fin']['Pitch'], height)
        # SMB ??? Hard coded value
        res_per_length = 67
        x_number = max( 1, int(round(((1000*unit_res)/(res_per_length*y_length)))))

        # ga = 2 if x_number == 1 else 1 ## when number of wires is 2 then large spacing req. so contact can be placed without a DRC error 
        # x_length = (x_number - 1) *ga*self.pdk['Cap']['m1Pitch']

        y_number = int(2 *round(((y_length+self.pdk['Cap']['m2Pitch']-self.pdk['Cap']['m2Width'])/(2.0*self.pdk['Cap']['m2Pitch']))))

        last_y1_track = ((y_number-1)*self.pdk['Cap']['m2Pitch']+self.pdk['M2']['Pitch']-1)//self.pdk['M2']['Pitch']
        last_x_track = x_number - 1

        m2factor = 2 ### number of m2-tracks (m2factor-1)in between two unitcells in y-direction
        m1factor = 3

        if (y_number-1) % 2 != last_y1_track % 2:
            last_y1_track += 1 # so the last color is compatible with the external view of the cell

        if last_y1_track % 2 == 1:
            m2factor += 1 # so colors match in arrayed blocks

        grid_cell_x_pitch = m1factor + last_x_track
        grid_cell_y_pitch = m2factor + last_y1_track

        grid_y0 = y*grid_cell_y_pitch
        grid_y1 = grid_y0 + last_y1_track

        for i in range(x_number):
            (k, p) = (2*i, 1) if x_number==2 else (i, 0)
            grid_x = k + x*grid_cell_x_pitch

            self.addWire( self.m1res, None, grid_x, (grid_y0, -1), (grid_y1, 1))
            if i < x_number-1:
                grid_yh = ((i+1)%2)*last_y1_track
                self.addWire( self.m1res2, None, grid_yh, (i, -1), (i+p+1, 1))

#
# Build the narrow m2 pitch grid starting at grid_cell_y_pitch*y in standard m2 pitch grids (m2.clg)
#
        m2n = Wire( self.m2res2.nm, self.m2res2.layer, self.m2res2.direction,
                    clg=self.m2res2.clg.copyShift( self.m2res.clg.value( grid_cell_y_pitch*y)[0]),
                    spg=self.m2res2.spg)

        grid_x0 = x*grid_cell_x_pitch
        grid_x1 = grid_x0 + last_x_track
        grid_y = (x_number%2)*last_y1_track

        pin = 'PLUS'
        self.addWire( m2n, 'PLUS', 0, (-4, -1), (0, 1), netType = 'pin')
        self.addVia( self.v1res, None, 0, 0)
        pin = 'MINUS'
        self.addWire( self.m2res, 'MINUS', grid_y, (grid_x1+p, -1), (grid_x1+p+4, 1), netType = 'pin')
        self.addVia( self.v1res, None, grid_x1+p, grid_y)

        if draw_boundary:
            self.addRegion( self.boundary, 'boundary', -4, -1,
                            last_x_track  + x * grid_cell_x_pitch + 4 + p,
                            last_y1_track + y * grid_cell_y_pitch + 1)

            self.addRegion( self.Rboundary, 'Rboundary', -1, -1,
                            last_x_track  + x * grid_cell_x_pitch + 4 + p,
                            last_y1_track + y * grid_cell_y_pitch + 1)
