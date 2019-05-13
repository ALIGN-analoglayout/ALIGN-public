import sys
import json
import math
import argparse
import os
from os import system
import transformation
import gen_json_gds
import gen_lef

class StopPointGrid:
    def __init__( self, nm, layer, direction, width, pitch, offset=0):
        self.nm = nm
        self.layer = layer
        self.direction = direction
        assert direction in ['v','h']
        self.width = width
        self.pitch = pitch
        self.offset = offset
        assert pitch > width > 0

        self.grid = []
        self.legalStopVector = []
        self.legalStopIndices = set()

    def addGridPoint( self, value, isLegal):
        self.grid.append( value)
        self.legalStopVector.append( isLegal)
        if isLegal:
            self.legalStopIndices.add( len(self.grid)-1)

    @property
    def n( self):
        return len(self.grid)-1

    def value( self, idx):
        whole = idx // self.n
        fract = idx % self.n
        while fract < 0:
            whole -= 1
            fract += self.n
        assert fract in self.legalStopIndices
        return whole * self.grid[-1] + self.grid[fract]

    def segment( self, netName, pinName, center, bIdx, eIdx):
        c = center*self.pitch + self.offset
        c0 = c - self.width//2
        c1 = c + self.width//2
        if self.direction == 'h':
           # rect = [ self.value(bIdx), c0, self.value(eIdx), c1]
             rect = [ bIdx, c0, eIdx, c1]
        else:
           # rect = [ c0, self.value(bIdx), c1, self.value(eIdx)]
             rect = [ c0, bIdx, c1, eIdx]
        return { 'netName' : netName, 'pin' : pinName, 'layer' : self.layer, 'rect' : rect}

    def segment1( self, netName, pinName, bIdy, eIdy, bIdx, eIdx):
        rect = [bIdx, bIdy, eIdx, eIdy]
        return { 'netName' : netName, 'pin' : pinName, 'layer' : self.layer, 'rect' : rect}

class UnitCell:

    def computeBbox( self):
        self.bbox = transformation.Rect(None,None,None,None)
        for term in self.terminals:
            r = transformation.Rect( *term['rect'])
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

    def __init__( self):
        self.terminals = []
        self.dcPitch = 80
        self.dcWidth = 40
        self.m0Width = 32
        self.m0Pitch = 64
        self.m0Offset = 0
        self.plOffset = 0
        self.plWidth = 20

        self.plPitch = 80
        self.m1Pitch = 64 
        self.m1Width = 32
        self.m2Pitch = 64
        self.m2Pitch1 = 84
        self.m2factor = 2 ### number of m2-tracks (self.m2factor-1)in between two unitcells in y-direction
        self.m1factor = 3
        self.m2Width = 32
        self.m3Pitch = 64 
        self.m3Width = 32
        self.v1Pitch  = self.m2Pitch ### Same as m2Pitch
        self.v1Width = 32
        self.v2Pitch  = self.m2Pitch ### Same as m2Pitch
        self.v2Width = 32        
        self.v1_enclosure = 20
 
        self.m1Offset = 0
        self.m2Offset = 0
        self.m3Offset = self.m1Offset             

        stoppoint = (self.dcWidth//2 + self.plOffset-self.plWidth//2)//2
        self.m0 = StopPointGrid( 'm0', 'M0', 'v', width=self.m0Width, pitch=self.m0Pitch,offset=self.m0Offset)
        self.m0.addGridPoint( 0,                 False)
        self.m0.addGridPoint( stoppoint,         True)
        self.m0.addGridPoint( self.plOffset,          False)
        self.m0.addGridPoint( self.dcPitch-stoppoint, True)
        self.m0.addGridPoint( self.dcPitch,           False)

        self.m1c1 = StopPointGrid( 'm1', 'M1', 'v', width=self.m1Width, pitch=self.m1Pitch, offset=self.m1Offset)
        self.m1c1.addGridPoint( 0,                   False)
        self.m1c1.addGridPoint( stoppoint,           True)
        self.m1c1.addGridPoint( 2*self.m0Pitch,           False)
        self.m1c1.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m1c1.addGridPoint( 4*self.m0Pitch,           False)

        self.m1c2 = StopPointGrid( 'm1', 'M1', 'v', width=self.m1Width, pitch=self.m1Pitch, offset=self.m1Offset)
        self.m1c2.addGridPoint( 0,                   False)
        self.m1c2.addGridPoint( stoppoint,           True)
        self.m1c2.addGridPoint( 2*self.m0Pitch,           False)
        self.m1c2.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m1c2.addGridPoint( 4*self.m0Pitch,           False)
        
        self.m2c1 = StopPointGrid( 'm2', 'M2', 'h', width=self.m2Width, pitch=self.m2Pitch, offset=self.m2Offset)
        self.m2c1.addGridPoint( 0,                 False)
        self.m2c1.addGridPoint( stoppoint,         True)
        self.m2c1.addGridPoint( 2*self.m0Pitch,          False)
        self.m2c1.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m2c1.addGridPoint( 4*self.m0Pitch,           False)

        self.m2c2 = StopPointGrid( 'm2', 'M2', 'h', width=self.m2Width, pitch=self.m2Pitch, offset=self.m2Offset)
        self.m2c2.addGridPoint( 0,                 False)
        self.m2c2.addGridPoint( stoppoint,         True)
        self.m2c2.addGridPoint( 2*self.m0Pitch,          False)
        self.m2c2.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m2c2.addGridPoint( 4*self.m0Pitch,           False)

        self.m3c1 = StopPointGrid( 'm3', 'M3', 'v', width=self.m3Width, pitch=self.m3Pitch, offset=self.m3Offset)
        self.m3c1.addGridPoint( 0,                   False)
        self.m3c1.addGridPoint( stoppoint,           True)
        self.m3c1.addGridPoint( 2*self.m0Pitch,           False)
        self.m3c1.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m3c1.addGridPoint( 4*self.m0Pitch,           False)

        self.m3c2 = StopPointGrid( 'm3', 'M3', 'v', width=self.m3Width, pitch=self.m3Pitch, offset=self.m3Offset)
        self.m3c2.addGridPoint( 0,                   False)
        self.m3c2.addGridPoint( stoppoint,           True)
        self.m3c2.addGridPoint( 2*self.m0Pitch,           False)
        self.m3c2.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.m3c2.addGridPoint( 4*self.m0Pitch,           False)

        self.pl = StopPointGrid( 'pl', 'poly', 'v', width=self.plWidth, pitch=self.plPitch, offset=self.plOffset)
        self.pl.addGridPoint( 0,                   False)
        self.pl.addGridPoint( stoppoint,           True)
        self.pl.addGridPoint( 2*self.m0Pitch,           False)
        self.pl.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.pl.addGridPoint( 4*self.m0Pitch,           False)


        
        self.v1 = StopPointGrid( 'v1', 'via1', 'v', width=self.v1Width, pitch=self.v1Pitch, offset=self.m2Offset)
        self.v1.addGridPoint( 0,                   False)
        self.v1.addGridPoint( stoppoint,           True)
        self.v1.addGridPoint( 2*self.m0Pitch,           False)
        self.v1.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.v1.addGridPoint( 4*self.m0Pitch,           False)

        self.v2 = StopPointGrid( 'v2', 'via2', 'v', width=self.v2Width, pitch=self.v2Pitch, offset=self.m2Offset)
        self.v2.addGridPoint( 0,                   False)
        self.v2.addGridPoint( stoppoint,           True)
        self.v2.addGridPoint( 2*self.m0Pitch,           False)
        self.v2.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.v2.addGridPoint( 4*self.m0Pitch,           False)

        self.boundary = StopPointGrid( 'nwell', 'nwell', 'v', width=self.m1Width, pitch=self.m1Pitch, offset=self.m1Offset)


    def addSegment( self, grid, netName, pinName, c, bIdx, eIdx):
        segment = grid.segment( netName, pinName, c, bIdx, eIdx)
        self.terminals.append( segment)
        return segment
        
    def addSegment1( self, grid, netName, pinName, bIdy, eIdy, bIdx, eIdx):
        segment1 = grid.segment1( netName, pinName, bIdy, eIdy, bIdx, eIdx)
        self.terminals.append( segment1)
        return segment1

    def m0Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m0, netName, pinName, x, y0, y1)
    def m1c1Segment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.m1c1, netName, pinName, y0, y1, x0, x1)
    def m1c2Segment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.m1c2, netName, pinName, y0, y1, x0, x1)
    def m2c1Segment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.m2c1, netName, pinName, y0, y1, x0, x1)
    def m2c2Segment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.m2c2, netName, pinName, y0, y1, x0, x1)
    def m3c1Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m3c1, netName, pinName, x, y0, y1)
    def m3c2Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m3c2, netName, pinName, x, y0, y1)
    def plSegment( self, netName, pinName, x, y0, y1): return self.addSegment( self.pl, netName, pinName, x, y0, y1)
    def v1Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.v1, netName, pinName, x, y0, y1)
    def v2Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.v2, netName, pinName, x, y0, y1)
    def boundarySegment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.boundary, netName, pinName, y0, y1, x0, x1)

    def unit( self, x, y):

        x_number = int(round(((1000*input_resistance)/(res_per_length*y_length))))        
        (ga, gb) = (2, 0) if x_number == 2 else (1, -1) ## when number of wires is 2 then large spacing req. so contact can be placed without a DRC error
        x_length = (x_number - 1) *ga*self.m1Pitch 

        for i in range(x_number):
            #if i == 0 or (i == x_number-1 and (x_number-1)%2 !=0):
            if i == 0 or i == x_number-1:
                uc.m1c1Segment( 'm1', 'NA', (y*y_length - self.m2Width/2 - self.v1_enclosure), ((1+y)*y_length + self.m2Width/2 + self.v1_enclosure), ((i + x*x_number + x)*ga*self.m1Pitch - self.m1Width/2), ((i + x*x_number + x)*ga*self.m1Pitch + self.m1Width/2))
            #elif i == x_number-1 and (x_number-1)%2 == 0:
            #    uc.m1c1Segment( 'm1', 'NA', (y*y_length - self.m2Width/2 ), ((1+y)*y_length + self.m2Width/2 + self.v1_enclosure), ((i + x*x_number + x)*self.m1Pitch - self.m1Width/2), ((i + x*x_number + x)*self.m1Pitch + self.m1Width/2))
            
            else:
                uc.m1c1Segment( 'm1', 'NA', (y*y_length - self.m2Width/2), ((1+y)*y_length + self.m2Width/2), ((i + x*x_number + x)*ga*self.m1Pitch - self.m1Width/2), ((i + x*x_number + x)*ga*self.m1Pitch + self.m1Width/2))
            if i < x_number-1:
                if (i % 2) == 0:
                    uc.m1c1Segment( 'm1', 'NA', ((1+y)*y_length - self.m1Width/2), ((1+y)*y_length + self.m1Width/2), ((i + x*x_number + x)*ga*self.m1Pitch - self.m1Width/2), ((i + 1 + x*x_number + x)*ga*self.m1Pitch + self.m1Width/2))                
                else:
                    uc.m1c1Segment( 'm1', 'NA', (-self.m1Width/2), (self.m1Width/2), ((i + x*x_number + x)*ga*self.m1Pitch - self.m1Width/2), ((i + 1 + x*x_number + x)*ga*self.m1Pitch + self.m1Width/2))
                
        
        uc.v1Segment( 'v1','NA', (x*x_number + x), (y*y_length - self.v1Width/2), (y*y_length + self.v1Width/2))
        uc.m2c1Segment( 'm2', 'PLUS', (-self.m2Width/2), (self.m2Width/2), (x*x_length - self.m1Pitch), (x*x_length + self.m2Width/2 + self.v1_enclosure))

        if (x_number-1)%2 == 0:
            uc.m2c1Segment( 'm2', 'MINUS', ((1+y)*y_length - self.m2Width/2), ((1+y)*y_length + self.m2Width/2), ((1+x)*x_length - self.m1Width/2 - self.v1_enclosure), ((1+x)*x_length + self.m1Pitch))
            uc.v1Segment( 'v1', 'NA', (x_number + gb + x*x_number + x), ((1+y)*y_length - self.v1Width/2), ((1+y)*y_length) + self.v1Width/2)
        else:
            uc.m2c1Segment( 'm2', 'MINUS', (y*y_length - self.m2Width/2), (y*y_length + self.m2Width/2), ((1+x)*x_length - self.m1Width/2 - self.v1_enclosure), ((1+x)*x_length + self.m1Pitch))
            uc.v1Segment( 'v1','NA', (x_number + gb + x*x_number + x), (y*y_length - self.v1Width/2), (y*y_length + self.v1Width/2))

        if x == x_cells -1 and y == y_cells -1:            
            uc.boundarySegment( 'boundary', 'NA', (-self.m2Pitch1), ((1+y)*y_length + (1+2*y)*self.m2Pitch1), (-self.m1Pitch), (x_length*(1+x) + self.m1factor*x*self.m1Pitch + self.m1Pitch)) ####Cellarea

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
    uc = UnitCell()

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y)

    uc.computeBbox()

    with open( "./Viewer/INPUT/mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
    gen_json_gds.json_gds("./Viewer/INPUT/mydesign_dr_globalrouting.json",args.block_name)
    cell_pin = ["PLUS", "MINUS"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    system('python3 setup.py build_ext --inplace')
    system('python3 gen_gds.py -j %s.json -n %s -e MTI' % (args.block_name,args.block_name))


