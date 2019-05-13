import sys
import json
import argparse
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

    def __init__( self ):
        self.terminals = []
        ##### PDK Abstraction   ##### 
        self.dcPitch = 36 ### not in use for ASAP-7
        self.dcWidth = 32

        self.plPitch = 80 ### Use from DRM
        self.plWidth = 14
        self.finPitch = 42 ### finPitch from DRM
        self.finWidth = 10
        self.m0Pitch = self.plPitch
        self.m0Width = 34
        self.m1Pitch = self.plPitch ### Distance between Source and Drain 
        self.m1Width = 32
        self.m2Pitch = 84 ### Can be directly used from DRM (usually twice of the fin pitch)
        self.m2Width = 32
        self.m3Pitch = self.plPitch ### Use same as for m1
        self.m3Width = 32
        self.v0Pitch  = 126 ### V0 spacing rule
        self.v0Width = 32
        self.v1Pitch  = self.m2Pitch ### Same as m2Pitch
        self.v1Width = 32
        self.v2Pitch  = self.m2Pitch ### Same as m2Pitch
        self.v2Width = 32        
        self.tbPitch = self.plPitch ### Use same as for poly
        self.tbWidth = 60
        

        self.gcutWidth = 94
        self.pcWidth = 18
        self.pc_activeDistance = 30 ### Minimum corner-to-corner spacing between two V0
        self.gcut_activeDistance = 55 
        self.pc_gcutDistance = 5    ### Minimum distance between LIG and gate cut
        self.plActive_s = 73 ### Active horizontal extension over the Gate
        self.plActive = 7
        self.v_enclosure = 20
        self.fin_enclosure = (self.finPitch - self.finWidth)/2 ### Fin enclosure by active
        self.active_enclosure = 42
        self.pc_gateExtension = 1 ###Minimum extension of LIG over GATE on both opposite sides

        self.plOffset = 0
        self.finOffset = 0  
        self.m0Offset = self.plPitch/2
        self.m1Offset = self.plPitch/2
        self.m2Offset = -self.m2Pitch/2
        self.m3Offset = self.m1Offset
        self.tbOffset = 0 
                
        
        self.finDummy = 5  ### Number of dummy fins
        self.gateDummy = 3 ### Number of dummy gates
        self.gate = int(round(gate_u + 2*self.gateDummy)) #### Total number of gates per unit cell
        self.extension_x = (self.plPitch - self.plWidth)/2  ### Minimum horizontal extension of GCUT past GATE
        self.activeWidth1 = self.finPitch*fin_u
        self.activeWidth = self.finPitch*fin_u1
        self.activeWidth_h = ((gate_u-1)* self.plPitch) + (self.plActive_s * 2) + self.plWidth
        self.activePitch = self.activeWidth1 + 2*self.finDummy*self.finPitch
        self.activeOffset = (self.activeWidth/2) + self.finDummy*self.finPitch - self.fin_enclosure -self.finWidth/2 + self.finOffset
        self.RVTWidth = self.activeWidth + 2*self.active_enclosure
        self.RVTPitch = self.activePitch
        self.RVTOffset = (self.RVTWidth/2) + self.finDummy*self.finPitch - self.fin_enclosure - self.active_enclosure -self.finWidth/2 + self.finOffset
        self.pcLength = (gate_u-1)*self.plPitch + self.plWidth + (2*self.pc_gateExtension)
        self.pcPitch  = self.activePitch
        self.pcOffset = (self.finPitch*fin_u+ + self.pcWidth/2 + self.finWidth + self.fin_enclosure + self.pc_activeDistance)
        self.gcutPitch  = self.activePitch
        self.gcutOffset =  self.activeOffset + self.gcut_activeDistance + self.gcutWidth/2 + self.activeWidth/2
        self.gcut1Offset =  self.finDummy*self.finPitch - self.fin_enclosure - self.gcut_activeDistance - self.gcutWidth/2
        

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

        self.AUX = StopPointGrid( 'AUX', 'M3', 'v', width=self.plWidth, pitch=self.plPitch, offset=self.plOffset)
        self.AUX.addGridPoint( 0,                   False)
        self.AUX.addGridPoint( stoppoint,           True)
        self.AUX.addGridPoint( 2*self.m0Pitch,           False)
        self.AUX.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.AUX.addGridPoint( 4*self.m0Pitch,           False)

        self.tb = StopPointGrid( 'tb', 'poly', 'v', width=self.tbWidth, pitch=self.tbPitch, offset=self.tbOffset)
        self.tb.addGridPoint( 0,                   False)
        self.tb.addGridPoint( stoppoint,           True)
        self.tb.addGridPoint( 2*self.m0Pitch,           False)
        self.tb.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.tb.addGridPoint( 4*self.m0Pitch,           False)

        self.dc = StopPointGrid( 'dc', 'diffcon', 'v', width=self.dcWidth, pitch=self.dcPitch)
        self.dc.addGridPoint( 0,                   False)
        self.dc.addGridPoint( stoppoint,           True)
        self.dc.addGridPoint( 2*self.m0Pitch,           False)
        self.dc.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.dc.addGridPoint( 4*self.m0Pitch,           False)

        self.v0 = StopPointGrid( 'v0', 'via0', 'v', width=self.v0Width, pitch=self.v0Pitch)
        self.v0.addGridPoint( 0,                   False)
        self.v0.addGridPoint( stoppoint,           True)
        self.v0.addGridPoint( 2*self.m0Pitch,           False)
        self.v0.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.v0.addGridPoint( 4*self.m0Pitch,           False)
        
        self.v1 = StopPointGrid( 'v1', 'via1', 'h', width=self.v1Width, pitch=self.v1Pitch, offset=self.m2Offset)
        self.v1.addGridPoint( 0,                   False)
        self.v1.addGridPoint( stoppoint,           True)
        self.v1.addGridPoint( 2*self.m0Pitch,           False)
        self.v1.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.v1.addGridPoint( 4*self.m0Pitch,           False)

        self.v2 = StopPointGrid( 'v2', 'via2', 'h', width=self.v2Width, pitch=self.v2Pitch, offset=self.m2Offset)
        self.v2.addGridPoint( 0,                   False)
        self.v2.addGridPoint( stoppoint,           True)
        self.v2.addGridPoint( 2*self.m0Pitch,           False)
        self.v2.addGridPoint( 4*self.m0Pitch-stoppoint, True)
        self.v2.addGridPoint( 4*self.m0Pitch,           False)
        
        self.fin = StopPointGrid( 'fin', 'fin', 'h', width=self.finWidth, pitch=self.finPitch, offset=self.finOffset)
        self.fin.addGridPoint( 0,                 False)
        self.fin.addGridPoint( stoppoint,         True)
        self.fin.addGridPoint( self.plOffset,          False)
        self.fin.addGridPoint( self.dcPitch-stoppoint, True)
        self.fin.addGridPoint( self.dcPitch,           False)

        self.active = StopPointGrid( 'active', 'active', 'h', width=self.activeWidth, pitch=self.activePitch, offset=self.activeOffset)
        self.active.addGridPoint( 0,                 False)
        self.active.addGridPoint( stoppoint,         True)
        self.active.addGridPoint( self.plOffset,          False)
        self.active.addGridPoint( self.dcPitch-stoppoint, True)
        self.active.addGridPoint( self.dcPitch,           False)

        self.RVT = StopPointGrid( 'RVT', 'polycon', 'h', width=self.RVTWidth, pitch=self.RVTPitch, offset=self.RVTOffset)
        self.RVT.addGridPoint( 0,                 False)
        self.RVT.addGridPoint( stoppoint,         True)
        self.RVT.addGridPoint( self.plOffset,          False)
        self.RVT.addGridPoint( self.dcPitch-stoppoint, True)
        self.RVT.addGridPoint( self.dcPitch,           False)

        self.nselect = StopPointGrid( 'nselect', 'nselect', 'v', width=self.activeWidth, pitch=self.activePitch, offset=self.activeOffset)

        self.pselect = StopPointGrid( 'pselect', 'pselect', 'v', width=self.activeWidth, pitch=self.activePitch, offset=self.activeOffset)

        self.nwell = StopPointGrid( 'nwell', 'nwell', 'v', width=self.activeWidth, pitch=self.activePitch, offset=self.activeOffset)

        self.gcut = StopPointGrid( 'GCUT', 'GCUT', 'h', width=self.gcutWidth, pitch=self.gcutPitch, offset=self.gcutOffset)
        self.gcut.addGridPoint( 0,                 False)
        self.gcut.addGridPoint( stoppoint,         True)
        self.gcut.addGridPoint( self.plOffset,          False)
        self.gcut.addGridPoint( self.dcPitch-stoppoint, True)
        self.gcut.addGridPoint( self.dcPitch,           False)

        self.gcut1 = StopPointGrid( 'GCUT', 'GCUT', 'h', width=self.gcutWidth, pitch=self.gcutPitch, offset=self.gcut1Offset)
        self.gcut1.addGridPoint( 0,                 False)
        self.gcut1.addGridPoint( stoppoint,         True)
        self.gcut1.addGridPoint( self.plOffset,          False)
        self.gcut1.addGridPoint( self.dcPitch-stoppoint, True)
        self.gcut1.addGridPoint( self.dcPitch,           False)

        self.pc = StopPointGrid( 'pc', 'polycon', 'h', width=self.pcWidth, pitch=self.pcPitch, offset=self.pcOffset)
        self.pc.addGridPoint( 0,                 False)
        self.pc.addGridPoint( stoppoint,         True)
        self.pc.addGridPoint( self.dcPitch//2,        False)
        self.pc.addGridPoint( self.dcPitch-stoppoint, True)
        self.pc.addGridPoint( self.dcPitch,           False)


    def addSegment( self, grid, netName, pinName, c, bIdx, eIdx):
        segment = grid.segment( netName, pinName, c, bIdx, eIdx)
        self.terminals.append( segment)
        return segment
        
    def addSegment1( self, grid, netName, pinName, bIdy, eIdy, bIdx, eIdx):
        segment1 = grid.segment1( netName, pinName, bIdy, eIdy, bIdx, eIdx)
        self.terminals.append( segment1)
        return segment1

    def m0Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m0, netName, pinName, x, y0, y1)
    def m1c1Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m1c1, netName, pinName, x, y0, y1)
    def m1c2Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m1c2, netName, pinName, x, y0, y1)
    def m2c1Segment( self, netName, pinName, x0, x1, y): return self.addSegment( self.m2c1, netName, pinName, y, x0, x1)
    def m2c2Segment( self, netName, pinName, x0, x1, y): return self.addSegment( self.m2c2, netName, pinName, y, x0, x1)
    def m3c1Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m3c1, netName, pinName, x, y0, y1)
    def m3c2Segment( self, netName, pinName, x, y0, y1): return self.addSegment( self.m3c2, netName, pinName, x, y0, y1)
    def plSegment( self, netName, pinName, x, y0, y1): return self.addSegment( self.pl, netName, pinName, x, y0, y1)
    def AUXSegment( self, netName, pinName, x, y0, y1): return self.addSegment( self.AUX, netName, pinName, x, y0, y1)
    def tbSegment( self, netName, pinName, x, y0, y1): return self.addSegment( self.tb, netName, pinName, x, y0, y1)
    def dcSegment( self, netName, pinName, x, y0, y1): return self.addSegment( self.dc, netName, pinName, x, y0, y1)
    def finSegment( self, netName, pinName, x0, x1, y): return self.addSegment( self.fin, netName, pinName, y, x0, x1)
    def activeSegment( self, netName, pinName, x0, x1, y): return self.addSegment( self.active, netName, pinName, y, x0, x1)
    def nselectSegment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.nselect, netName, pinName, y0, y1, x0, x1)
    def pselectSegment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.pselect, netName, pinName, y0, y1, x0, x1)
    def nwellSegment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.nwell, netName, pinName, y0, y1, x0, x1)
    def RVTSegment( self, netName, pinName, x0, x1, y): return self.addSegment( self.RVT, netName, pinName, y, x0, x1)
    def gcutSegment( self, netName, pinName, x0, x1, y): return self.addSegment( self.gcut, netName, pinName, y, x0, x1)
    def gcut1Segment( self, netName, pinName, x0, x1, y): return self.addSegment( self.gcut1, netName, pinName, y, x0, x1)
    def pcSegment( self, netName, pinName, x0, x1, y): return self.addSegment( self.pc, netName, pinName, y, x0, x1)
    def v0Segment( self, netName, pinName, y0, y1, x0, x1): return self.addSegment1( self.v0, netName, pinName, y0, y1, x0, x1)
    def v1Segment( self, netName, pinName, x0, x1, y): return self.addSegment( self.v1, netName, pinName, y, x0, x1)
    def v2Segment( self, netName, pinName, x0, x1, y): return self.addSegment( self.v2, netName, pinName, y, x0, x1)

    def unit( self, x, y):

        #####   Derived parameters   #####         
        fin = int(round(fin_u + 2*self.finDummy)) #### Total number of fins per unit cell    
        cont_no = int(round(self.activeWidth/self.v0Pitch)) ### number of V0 
        x_length = self.gate*self.plPitch
        y_length = fin * self.finPitch
        y_total = y_length*y_cells
        #m1Length = self.m2Width + (2*self.v_enclosure) + (self.m2Pitch*((fin_u+1)//2))
        m1Length = self.m2Width/2 + self.v_enclosure + (self.m2Pitch*((fin_u+2)//2))
        m1PCLength = self.m2Width + (2*self.v_enclosure) + (self.m2Pitch*((fin_u+3)//2))
        m2_tracks = int(round(y_total/self.m2Pitch)) ### Total number of M2-tracks 

         #####   This part generats locations of S/D/G   #####
        SA = []
        SB = []
        DA = []
        DB = []
        GA = []
        GB = []
        #for k in range(x_cells//2):
        #    if k%2 == 0:
        #        p = self.gateDummy - 1
        #    else:
        #        p = self.gate + self.gateDummy - 1
        #    lS = 2*k*self.gate + p
        #    lG = lS + 1
        #    SA.append(lS)
        #    GA.append(lG)
        #for k in range(x_cells//2):
        #    if k%2 == 0:
        #        p = self.gate + self.gateDummy - 1
        #    else:
        #        p = self.gateDummy - 1
        #    lS = 2*k*self.gate + p
        #    lG = lS + 1
        #    SB.append(lS)
        #    GB.append(lG)

        for k in range(x_cells):
            lS = k*self.gate + self.gateDummy - 1
            lG = lS + 1
            lD = lS + gate_u             
            if k == (x_cells-2)//2 or k == ((x_cells-2)//2 + 1):
                SA.append(lS)
                DA.append(lD)
                GA.append(lG)
            else:
                DB.append(lD)
                SB.append(lS)
                GB.append(lG)

        S = SA + SB
        D = DA + DB
        G = GA + GB
        #print (SA)  

        #####   Active Layer   #####
        uc.activeSegment( 'active', 'NA', ((self.gateDummy - 1) * self.plPitch + x*x_length), (self.activeWidth_h + (self.gateDummy - 1) *self.plPitch + x*x_length), y) 

        #####   RVT   Layer   #####
        uc.RVTSegment( 'RVT', 'NA', ((self.gateDummy - 1) * self.plPitch + x*x_length), (self.activeWidth_h + (self.gateDummy - 1) *self.plPitch + x*x_length), y)

        #####   Gate Cut Layer   #####        
        #uc.gcutSegment( 'GCUT', 'NA', ((-self.plPitch/2)+ x*x_length), ((1+x)*x_length - self.plPitch/2), y)
        #uc.gcut1Segment( 'GCUT', 'NA', ((-self.plPitch/2)+ x*x_length), ((1+x)*x_length - self.plPitch/2), y) 

        #####   Poly Connect Layer   #####
        #uc.pcSegment( 'PC', ( self.plPitch - self.pc_gateExtension + x*x_length), (self.plPitch - self.pc_gateExtension + x*x_length + self.pcLength), y)

        #####   Active fins   #####
        for i in range(fin):  
            uc.finSegment( 'fin', 'NA', ((-self.plPitch/2)+ x*x_length), ((1+x)*x_length - self.plPitch/2), (i+y*fin))   

        #####   Gate Placement   #####
        for i in range(self.gate):
            if (y == y_cells-1):
                uc.plSegment( 'g', 'NA', (i+(x*self.gate)), (y*y_length - self.m2Pitch//2), ((1+y)*y_length + self.m2Pitch//2))
                                
            else:
                uc.plSegment( 'g', 'NA', (i+(x*self.gate)), (y*y_length - self.m2Pitch//2), ((1+y)*y_length - self.m2Pitch//2))
                

        #####   Nselect Placement   #####
        if x == x_cells -1 and y == y_cells -1:
            uc.nselectSegment( 'nselect', 'NA', -self.m2Pitch//2, ((y+1)*y_length + self.m2Pitch//2), (-self.plPitch//2), ((1+x)*(x_length) - self.plPitch//2)) ####Nselect Region


        for i in range(self.gate):
            if i < (self.gate-1):
                
                if i == (self.gateDummy-1) or i == (self.gateDummy + gate_u - 1): 
                    for j in range(cont_no):
                        uc.v0Segment( 'v0', 'NA', (self.finDummy*self.finPitch - self.fin_enclosure - self.finWidth/2 + self.finOffset + j*self.v0Pitch + y* self.activePitch), (self.finDummy*self.finPitch - self.fin_enclosure - self.finWidth/2 + self.finOffset + j*self.v0Pitch + y* self.activePitch + self.v0Width ), (self.m1Offset - (self.m1Width/2) + i*self.m1Pitch + x*self.gate*self.plPitch), (self.m1Offset - (self.m1Width/2) + i*self.m1Pitch +x*self.gate*self.plPitch + self.v0Width) )
                #else:
                  
                    #uc.v0Segment( 'v0', (self.activeWidth1 + self.finPitch - self.fin_enclosure + self.pc_activeDistance + y*self.pcPitch), (self.activeWidth1 + self.finPitch - self.fin_enclosure + self.pc_activeDistance + y*self.pcPitch + self.v0Width), (self.m1Offset - (self.m1Width/2) + i*self.m1Pitch + x*self.gate*self.plPitch), (self.m1Offset - (self.m1Width/2) + i*self.m1Pitch + x*self.gate*self.plPitch + self.v0Width) )


############### M2 routing ###########################
        

        for i in range((m2_tracks+1)):

            #if i == (2*y*(m2_tracks //y_cells + K_space)):
            #    uc.m2Segment( 'm2', 'GND', (((x-1)*extension_x)+ x*x_length), ((1+x)*(x_length)+x*extension_x), i)

            #if i == ((2*y+1)*(m2_tracks //y_cells + K_space)):
            #    uc.m2Segment( 'm2', 'VDD', (((x-1)*extension_x)+ x*x_length), ((1+x)*(x_length)+x*extension_x), i)
            #(zz) = ('c1Segment') if i%2 == 0 else ('c2Segment')
            
            if x_cells > 1 and x == 0 and i == (y*(m2_tracks //y_cells) + self.finDummy//2 + 0):
                if i%2 == 0:
                    uc.m2c1Segment( 'm2', 'GB', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
                else:
                    uc.m2c2Segment( 'm2', 'GB', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
         
            if x_cells > 1 and x == 0 and i == (y*(m2_tracks //y_cells) + self.finDummy//2 + 1):
                if i%2 == 0:
                    uc.m2c1Segment( 'm2', 'S', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
                else:
                    uc.m2c2Segment( 'm2', 'S', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)

            if x_cells > 1 and x == 0 and i == (y*(m2_tracks //y_cells) + self.finDummy//2 + 2):
                if i%2 == 0:
                    uc.m2c1Segment( 'm2', 'DA', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
                else:
                    uc.m2c2Segment( 'm2', 'DA', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)

            if x_cells > 1 and x == 0 and i == (y*(m2_tracks //y_cells) + self.finDummy//2 + 4):
                if i%2 == 0:
                    uc.m2c1Segment( 'm2', 'DB', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
                else:
                    uc.m2c2Segment( 'm2', 'DB', (self.m1Offset + (self.gateDummy-1)*self.plPitch - self.m1Width/2 - self.v_enclosure), (self.m1Offset + (x_cells*self.gate - 2*self.gateDummy + 2)*self.plPitch + self.m1Width/2 + self.v_enclosure), i)
                                                     
################# M1 routing ######################
        if (x_cells - 1 - x) == 0:
            for i in S + D:
                uc.m0Segment( 'm0', 'NA', i, (self.activeOffset - self.activeWidth/2 + y*self.activePitch), (self.activeOffset + self.activeWidth/2 + y*self.activePitch))
                (SD) = ('S') if i in S else ('D')
                if i%2 == 0: 
                    uc.m1c1Segment( SD, 'NA', i, ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset - self.m2Width/2 - self.v_enclosure), ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset + m1Length))
                else:
                    uc.m1c2Segment( SD, 'NA', i, ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset - self.m2Width/2 - self.v_enclosure), ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset + m1Length))

            for i in G:
                if i%2 == 0: 
                    uc.m1c1Segment( 'm1', 'NA', i, ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset - self.m2Width/2 - self.v_enclosure), ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset + m1Length))
                else:
                    uc.m1c2Segment( 'm1', 'NA', i, ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset - self.m2Width/2 - self.v_enclosure), ((y*(m2_tracks //y_cells) + self.finDummy//2)*self.m2Pitch + self.m2Offset + m1Length))
######## Vias placement ########
        if (x_cells - 1 - x) == 0:
            for i in S:
                uc.v1Segment( 'v1', 'NA', (i*self.m1Pitch + self.m1Offset - self.v1Width/2), (i*self.m1Pitch + self.m1Offset + self.v1Width -   self.v1Width/2), (y*(m2_tracks //y_cells) + self.finDummy//2 + 1))
            for i in GB:
                uc.v1Segment( 'v1', 'NA', (i*self.m1Pitch + self.m1Offset - self.v1Width/2), (i*self.m1Pitch + self.m1Offset + self.v1Width -   self.v1Width/2), (y*(m2_tracks //y_cells) + self.finDummy//2 + 0))
   
            (da,db) = (2, 4) if y % 2 == 0 else (4,2)
            
            for i in DA + GA:                    
                uc.v1Segment( 'v1', 'NA', (i*self.m1Pitch + self.m1Offset - self.v1Width/2), (i*self.m1Pitch + self.m1Offset + self.v1Width -   self.v1Width/2), (y*(m2_tracks //y_cells) + self.finDummy//2 + da))
            for i in DB:                    
                uc.v1Segment( 'v1', 'NA', (i*self.m1Pitch + self.m1Offset - self.v1Width/2), (i*self.m1Pitch + self.m1Offset + self.v1Width -   self.v1Width/2), (y*(m2_tracks //y_cells) + self.finDummy//2 + db))

         
      
                        
                                   
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    fin_u1 = args.nfin
    x_cells = 2*args.Xcells
    x_cells = x_cells + 2
    y_cells = 1
    #gate_u = int(sys.argv[4])
    gate_u = 2
    if fin_u1%2 != 0:
        fin_u = fin_u1 + 1
    else:
        fin_u = fin_u1 
    uc = UnitCell()

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y)

    uc.computeBbox()

    with open( "./Viewer/INPUT/mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
    gen_json_gds.json_gds("./Viewer/INPUT/mydesign_dr_globalrouting.json",args.block_name)
    cell_pin = ["S","DA", "DB", "GB"]
    gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    system('python3 setup.py build_ext --inplace')
    system('python3 gen_gds.py -j %s.json -n %s -e MTI' % (args.block_name,args.block_name))
