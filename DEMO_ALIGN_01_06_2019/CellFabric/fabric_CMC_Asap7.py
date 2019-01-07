
import json
import transformation
#Number of gates per unit cell 
gate_u = 2
#Number of fins per unit cell 
fin_u = 10
#Number of unit cells in x-direction 
#x_units = 2
#Number of unit cells in y-direction 
y_cells = 2
x_cells = 4

#gate = float(input("Enter the number of gates: "))
#fin = float(input("Enter the number of fins: "))
#x_units = float((input("number of unitcells in x direction: ")))
#y_units = float((input("number of unitcells in y direction: ")))
class StopPointGrid:
    def __init__( self, nm, layer, direction, *, width, pitch, offset=0):
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

    def segment( self, netName, center, bIdx, eIdx):
        c = center*self.pitch + self.offset
        c0 = c - self.width//2
        c1 = c + self.width//2
        if self.direction == 'h':
           # rect = [ self.value(bIdx), c0, self.value(eIdx), c1]
             rect = [ bIdx, c0, eIdx, c1]
        else:
           # rect = [ c0, self.value(bIdx), c1, self.value(eIdx)]
             rect = [ c0, bIdx, c1, eIdx]
        return { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

    def segment1( self, netName, bIdy, eIdy, bIdx, eIdx):
        rect = [bIdx, bIdy, eIdx, eIdy]
        return { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

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
        global gate_u
        global fin_u
        m0Pitch  = 54
        m1Pitch  = 54 
        m2Pitch  = 64 
        m3Pitch  = 54
        plPitch  = 54
        plOffset = 10
        m1Offset = 37
        m2Offset = 9
        m3Offset = 37
        v0Pitch  = 36
        v1Pitch  = 64
        v2Pitch  = 64
        #plOffset = plPitch//2
        dcPitch  = 36
        finPitch = 27
        #assert dcPitch == plPitch

        m0Width = 18
        m1Width = 18
        m2Width = 18
        m3Width = 18
        dcWidth = 18
        plWidth = 20
        v0Width = 18
        v1Width = 18
        v2Width = 18
        finWidth = 7
        gcutWidth = 18
        pcWidth = 18
        plActive = 25
        extension_y = 37
        fin_enclosure = 10
        activeWidth = finPitch*fin_u
        activePitch = activeWidth + 4*finPitch
        gcutPitch  = finPitch*fin_u + fin_enclosure + finWidth + extension_y + pcWidth + gcutWidth + 30 - 12
        pcPitch  = finPitch*fin_u + fin_enclosure + finWidth + extension_y + pcWidth + 30 + 6

        stoppoint = (dcWidth//2 + plOffset-plWidth//2)//2
        self.m0 = StopPointGrid( 'm0', 'metal0', 'h', width=m0Width, pitch=m0Pitch)
        self.m0.addGridPoint( 0,                 False)
        self.m0.addGridPoint( stoppoint,         True)
        self.m0.addGridPoint( plOffset,          False)
        self.m0.addGridPoint( dcPitch-stoppoint, True)
        self.m0.addGridPoint( dcPitch,           False)

        self.m1 = StopPointGrid( 'm1', 'metal1', 'v', width=m1Width, pitch=m1Pitch, offset=m1Offset)
        self.m1.addGridPoint( 0,                   False)
        self.m1.addGridPoint( stoppoint,           True)
        self.m1.addGridPoint( 2*m0Pitch,           False)
        self.m1.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.m1.addGridPoint( 4*m0Pitch,           False)
        
        self.m2 = StopPointGrid( 'm2', 'metal2', 'h', width=m2Width, pitch=m2Pitch, offset=m2Offset)
        self.m2.addGridPoint( 0,                 False)
        self.m2.addGridPoint( stoppoint,         True)
        self.m2.addGridPoint( 2*m0Pitch,          False)
        self.m2.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.m2.addGridPoint( 4*m0Pitch,           False)

        self.m3 = StopPointGrid( 'm3', 'metal3', 'v', width=m3Width, pitch=m3Pitch, offset=m3Offset)
        self.m3.addGridPoint( 0,                   False)
        self.m3.addGridPoint( stoppoint,           True)
        self.m3.addGridPoint( 2*m0Pitch,           False)
        self.m3.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.m3.addGridPoint( 4*m0Pitch,           False)

        self.pl = StopPointGrid( 'pl', 'poly', 'v', width=plWidth, pitch=plPitch, offset=plOffset)
        self.pl.addGridPoint( 0,                   False)
        self.pl.addGridPoint( stoppoint,           True)
        self.pl.addGridPoint( 2*m0Pitch,           False)
        self.pl.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.pl.addGridPoint( 4*m0Pitch,           False)

        self.dc = StopPointGrid( 'dc', 'diffcon', 'v', width=dcWidth, pitch=dcPitch)
        self.dc.addGridPoint( 0,                   False)
        self.dc.addGridPoint( stoppoint,           True)
        self.dc.addGridPoint( 2*m0Pitch,           False)
        self.dc.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.dc.addGridPoint( 4*m0Pitch,           False)

        self.v0 = StopPointGrid( 'v0', 'via0', 'v', width=v0Width, pitch=v0Pitch)
        self.v0.addGridPoint( 0,                   False)
        self.v0.addGridPoint( stoppoint,           True)
        self.v0.addGridPoint( 2*m0Pitch,           False)
        self.v0.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.v0.addGridPoint( 4*m0Pitch,           False)
        
        self.v1 = StopPointGrid( 'v1', 'via1', 'h', width=v1Width, pitch=v1Pitch, offset=m2Offset)
        self.v1.addGridPoint( 0,                   False)
        self.v1.addGridPoint( stoppoint,           True)
        self.v1.addGridPoint( 2*m0Pitch,           False)
        self.v1.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.v1.addGridPoint( 4*m0Pitch,           False)

        self.v2 = StopPointGrid( 'v2', 'via2', 'h', width=v2Width, pitch=v2Pitch, offset=m2Offset)
        self.v2.addGridPoint( 0,                   False)
        self.v2.addGridPoint( stoppoint,           True)
        self.v2.addGridPoint( 2*m0Pitch,           False)
        self.v2.addGridPoint( 4*m0Pitch-stoppoint, True)
        self.v2.addGridPoint( 4*m0Pitch,           False)
        
        self.fin = StopPointGrid( 'fin', 'ndiff', 'h', width=finWidth, pitch=finPitch, offset=3.5)
        self.fin.addGridPoint( 0,                 False)
        self.fin.addGridPoint( stoppoint,         True)
        self.fin.addGridPoint( plOffset,          False)
        self.fin.addGridPoint( dcPitch-stoppoint, True)
        self.fin.addGridPoint( dcPitch,           False)

        self.active = StopPointGrid( 'active', 'ndiff', 'h', width=activeWidth, pitch=activePitch, offset=((activeWidth//2) + 17))
        self.active.addGridPoint( 0,                 False)
        self.active.addGridPoint( stoppoint,         True)
        self.active.addGridPoint( plOffset,          False)
        self.active.addGridPoint( dcPitch-stoppoint, True)
        self.active.addGridPoint( dcPitch,           False)

        self.gcut = StopPointGrid( 'GCUT', 'GCUT', 'h', width=gcutWidth, pitch=gcutPitch, offset=(finPitch*fin_u+ + pcWidth + finWidth + fin_enclosure + gcutWidth//2 + 30))
        self.gcut.addGridPoint( 0,                 False)
        self.gcut.addGridPoint( stoppoint,         True)
        self.gcut.addGridPoint( plOffset,          False)
        self.gcut.addGridPoint( dcPitch-stoppoint, True)
        self.gcut.addGridPoint( dcPitch,           False)

        self.pc = StopPointGrid( 'pc', 'polycon', 'h', width=pcWidth, pitch=pcPitch, offset=(finPitch*fin_u+ + pcWidth//2 + finWidth + fin_enclosure + 30))
        self.pc.addGridPoint( 0,                 False)
        self.pc.addGridPoint( stoppoint,         True)
        self.pc.addGridPoint( dcPitch//2,        False)
        self.pc.addGridPoint( dcPitch-stoppoint, True)
        self.pc.addGridPoint( dcPitch,           False)


    def addSegment( self, grid, netName, c, bIdx, eIdx):
        segment = grid.segment( netName, c, bIdx, eIdx)
        self.terminals.append( segment)
        return segment
        
    def addSegment1( self, grid, netName, bIdy, eIdy, bIdx, eIdx):
        segment1 = grid.segment1( netName, bIdy, eIdy, bIdx, eIdx)
        self.terminals.append( segment1)
        return segment1

    def m0Segment( self, netName, x0, x1, y): return self.addSegment( self.m0, netName, y, x0, x1)
    def m1Segment( self, netName, x, y0, y1): return self.addSegment( self.m1, netName, x, y0, y1)
    def m2Segment( self, netName, x0, x1, y): return self.addSegment( self.m2, netName, y, x0, x1)
    def m3Segment( self, netName, x, y0, y1): return self.addSegment( self.m3, netName, x, y0, y1)
    def plSegment( self, netName, x, y0, y1): return self.addSegment( self.pl, netName, x, y0, y1)
    def dcSegment( self, netName, x, y0, y1): return self.addSegment( self.dc, netName, x, y0, y1)
    def finSegment( self, netName, x0, x1, y): return self.addSegment( self.fin, netName, y, x0, x1)
    def activeSegment( self, netName, x0, x1, y): return self.addSegment( self.active, netName, y, x0, x1)
    def gcutSegment( self, netName, x0, x1, y): return self.addSegment( self.gcut, netName, y, x0, x1)
    def pcSegment( self, netName, x0, x1, y): return self.addSegment( self.pc, netName, y, x0, x1)
    def v0Segment( self, netName, y0, y1, x0, x1): return self.addSegment1( self.v0, netName, y0, y1, x0, x1)
    def v1Segment( self, netName, x0, x1, y): return self.addSegment( self.v1, netName, y, x0, x1)
    def v2Segment( self, netName, x0, x1, y): return self.addSegment( self.v2, netName, y, x0, x1)
    def unit( self, x, y):
        global gate_u
        global fin_u
        global y_cells
        global x_cells
        Pitch = 36
        m1Pitch = 54
        m1Offset = 37
        m2Pitch = 64
        width = 18
        v0Width = 18
        v1Width = 18
        pcWidth = 18
        v0Pitch = 36
        plPitch = 54
        finPitch = 27
        finWidth = 7
        plWidth = 20
        plActive = 25 
        plActive_s = 29 
        activePitch_h = 92
        extension_x = 17
        extension_y = 37
        fin_enclosure = 10
        fin = int(round(fin_u + 2))
        fin1 = int(round(fin_u + 1))
        gate = int(round(gate_u + 2)) 
        activeWidth_h = ((gate - 3)) * plPitch + (plActive * 2) + plWidth
        #activeWidth = finPitch*(fin - 1) + 2*(fin_enclosure) + finWidth 
        activeWidth = finPitch*fin_u
        activePitch = activeWidth + 4*finPitch
        cont_no = activeWidth//v0Pitch
        pcPitch  = finPitch*fin_u + fin_enclosure + finWidth + extension_y + pcWidth + 30 + 6
        x_length = ((gate-1)*plPitch) + plWidth + extension_x
        y_length = (fin-1)*finPitch + finWidth + extension_y
        y_total = (y_length-finWidth)*y_cells + 2*(y_cells-1)*finPitch
        m2_tracks = int(round(y_total/m2Pitch))

        SA = []
        SB = []
        DA = []
        DB = []
        GA = []
        GB = []
        for k in range((x_cells//2)-1):
            lA = 16*k
            lB = 4*(4*k+1)
            SA.append(lA)
            GA.append(lA+1)
            DA.append(lA+2)
            SB.append(lB)
            GB.append(lB+1)
            DB.append(lB+2)
            mA = 16*(k+1) - 4
            mB = 8*(2*k+1)
            if k !=((x_cells//2)-2) or (k % 2) == 0:
                SA.append(mA)
                GA.append(mA+1)
                DA.append(mA+2)
                SB.append(mB)
                GB.append(mB+1)
                DB.append(mB+2)

        for i in range(gate):
            uc.plSegment( 'g', (i+(x*gate)), ((y*y_length)+((y-1)*extension_y)), (((1+y)*y_length)+(y*extension_y)))
            #if (i % 2) == 0:
            if i < (gate-1):
                if i == 0:
                    uc.m1Segment( 'S', (i+(x*gate)), ((y*(y_length-extension_y))+(y*74)), (((1+y)*(y_length-extension_y))+(y*74)))
                if i == gate_u:
                    uc.m1Segment( 'D', (i+(x*gate)), ((y*(y_length-extension_y))+(y*74)), (((1+y)*(y_length-extension_y))+(y*74)))
                if i == 0 or i == gate_u: 
                    for j in range(cont_no):
                        uc.v0Segment( 'v0', (17 + j*v0Pitch + y* activePitch), (17 + + j*v0Pitch + v0Width + y* activePitch), (m1Offset - 9 + i*m1Pitch + x*gate*plPitch), (m1Offset - 9 + v0Width + i*m1Pitch +x*gate*plPitch) )
                else:
                    uc.m1Segment( 'm1', (i+(x*gate)), ((y*(y_length-extension_y + 31))+(y*(74-31))), (((1+y)*(y_length-extension_y + 31))+(y*(74-31))))
                    uc.v0Segment( 'v0', (y_length-extension_y + 31 + y*pcPitch- v0Width), (y_length-extension_y + 31 + y*pcPitch), (m1Offset - 9 + i*m1Pitch + x*gate*plPitch), (m1Offset - 9 + v0Width + i*m1Pitch +x*gate*plPitch) )
            elif (x_cells-1-x) != 0:
               uc.m1Segment( 'm1', (i+(x*gate)), ((y*y_length)+((y-1)*extension_y)), (((1+y)*y_length)+(y*extension_y)))
               uc.m3Segment( 'm3', (i+(x*gate)), ((y*y_length)+((y-1)*extension_y)), (((1+y)*y_length)+(y*extension_y)))
            else:   
            #uc.v1Segment( 'v1', i, (y_length1-v1_width), y_length1)
            #uc.v1Segment( 'v1', i, 0, v1_width)
                print("")
        for i in range(fin):  
            uc.finSegment( 'fin', (((x-1)*extension_x)+ x*x_length), ((1+x)*(x_length)+x*extension_x), (i+(y*fin)+2*y))

        for i in range(m2_tracks):
            if y == (y_cells-1):
                uc.m2Segment( 'm2', (((x-1)*extension_x)+ x*x_length), ((1+x)*(x_length)+x*extension_x), i)
        if (y_cells-1-y) != 0:
            uc.gcutSegment( 'GCUT', (((x-1)*extension_x)+ x*x_length), ((1+x)*(x_length)+x*extension_x), y) #### Gate Cut
        uc.activeSegment( 'active', (plActive_s+ x*(activeWidth_h+plActive_s) + x*(plPitch + 9)), ((1+x)*(activeWidth_h+plActive_s)+ x*(plPitch + 9)), y) ####Active Region
        uc.pcSegment( 'PC', ((1+x)*(plPitch - extension_x) + x*(gate_u*plPitch + plWidth + extension_x) + x*(plPitch-plWidth) ), ((1+x)*(gate_u*plPitch + plWidth + extension_x) + x*(plPitch - extension_x) + x*(plPitch-plWidth)), y) #### Poly Connect


##### Routing for CMC pair
        if (x_cells - 1 - x) == 0:
            if (y % 2) == 0:
                for i in DA:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 1)
            else:
                for i in DB:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset- (v1Width//2)), (i*m1Pitch + m1Offset + v1Width -(v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 1)
           
        if (x_cells - 1 - x) == 0:
            if (y % 2) == 0:
                for i in DB:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset- (v1Width//2)), (i*m1Pitch + m1Offset + v1Width -(v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 2)
            else:
                for i in DA:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 2)

        if (x_cells - 1 - x) == 0:
            for i in GA:
                uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 0)
        if (x_cells - 1 - x) == 0:
            for i in GB:
                uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 0)

        if (x_cells - 1 - x) == 0:
            if (y % 2) == 0:
                for i in SA:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 3)
            else:
                for i in SB:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset- (v1Width//2)), (i*m1Pitch + m1Offset + v1Width -(v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 3)

        if (x_cells - 1 - x) == 0:
            if (y % 2) == 0:
                for i in SB:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset - (v1Width//2)), (i*m1Pitch + m1Offset + v1Width - (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 4)
            else:
                for i in SA:
                    uc.v1Segment( 'v1', (i*m1Pitch + m1Offset- (v1Width//2)), (i*m1Pitch + m1Offset + v1Width -(v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 4)
        
        if (x_cells - 1 - x) != 0:
            if x == 0:
                uc.v1Segment('v1', (m1Offset + (gate - 1 + x*gate)*m1Pitch - (v1Width//2)), (m1Offset + (gate - 1 + x*gate)*m1Pitch + (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 0)
            if x == 1:
                uc.v2Segment('v2', (m1Offset + (gate - 1 + x*gate)*m1Pitch - (v1Width//2)), (m1Offset + (gate - 1 + x*gate)*m1Pitch + (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 1)
                uc.v1Segment('v1', (m1Offset + (gate - 1 + x*gate)*m1Pitch - (v1Width//2)), (m1Offset + (gate - 1 + x*gate)*m1Pitch + (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 2)
            if x == 2:
                uc.v2Segment('v2', (m1Offset + (gate - 1 + x*gate)*m1Pitch - (v1Width//2)), (m1Offset + (gate - 1 + x*gate)*m1Pitch + (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 3)
                uc.v1Segment('v1', (m1Offset + (gate - 1 + x*gate)*m1Pitch - (v1Width//2)), (m1Offset + (gate - 1 + x*gate)*m1Pitch + (v1Width//2)), y*(((m2_tracks-y_cells + 1)//y_cells)+1) + 4)
                
        

                

if __name__ == "__main__":
    uc = UnitCell()

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y)

    uc.computeBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
