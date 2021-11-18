import itertools

from align.cell_fabric import Via, Region, Canvas, Wire
from align.cell_fabric import UncoloredCenterLineGrid, ColoredCenterLineGrid
from align.cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid

class CanvasNMOS(Canvas):
    def __init__( self, gate_u, fin_u, fin_u1):
        super().__init__()

        ##### PDK Abstraction   ##### 

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
        self.v0Pitch  = 3*self.finPitch ### V0 spacing rule
        self.v0Width = 32

        self.plActive_s = 73 ### Active horizontal extension over the Gate
        self.plActive = 7
        self.v_enclosure = 20
        self.fin_enclosure = (self.finPitch - self.finWidth)//2 ### Fin enclosure by active
        self.active_enclosure = 42

        self.finOffset = 0  
        self.plOffset = 0
        
        self.finDummy = 5  ### Number of dummy fins
        self.gateDummy = 3 ### Number of dummy gates
        self.gate = int(round(gate_u + 2*self.gateDummy)) #### Total number of gates per unit cell
        self.extension_x = (self.plPitch - self.plWidth)//2  ### Minimum horizontal extension of GCUT past GATE
        self.activeWidth = self.finPitch*fin_u1
        self.activeWidth_h = ((gate_u-1)* self.plPitch) + (self.plActive_s * 2) + self.plWidth
        self.activePitch = self.finPitch*(fin_u + 2*self.finDummy)
        self.activeOffset = (self.activeWidth//2) + self.finDummy*self.finPitch - self.fin_enclosure -self.finWidth//2 + self.finOffset
        self.RVTWidth = self.activeWidth + 2*self.active_enclosure
        self.RVTPitch = self.activePitch
        self.RVTOffset = (self.RVTWidth//2) + self.finDummy*self.finPitch - self.fin_enclosure - self.active_enclosure -self.finWidth//2 + self.finOffset

        self.m0 = self.addGen( Wire( 'm0', 'M0', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=self.m0Pitch, width=self.m0Width, offset=self.m0Pitch//2),
                                     spg=EnclosureGrid( pitch=self.activePitch, offset=self.activeOffset, stoppoint=self.activeWidth//2, check=True)))

        self.m1 = self.addGen( Wire( 'm1', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.m1Pitch, width=self.m1Width, offset=self.m1Pitch//2),
                                     spg=EnclosureGrid( pitch=self.m2Pitch, offset=self.m2Pitch//2, stoppoint=self.m2Width//2 + self.v_enclosure, check=True)))

        self.m2 = self.addGen( Wire( 'm2', 'M2', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c2','c1'], pitch=self.m2Pitch, width=self.m2Width, offset=self.m2Pitch//2),
                                     spg=EnclosureGrid(pitch=self.m1Pitch, offset=self.m1Pitch//2, stoppoint=self.m1Width//2 + self.v_enclosure, check=True)))

        self.m3 = self.addGen( Wire( 'm3', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=self.m3Pitch, width=self.m3Width, offset=self.m3Pitch//2),
                                     spg=EnclosureGrid( pitch=self.m2Pitch, offset=self.m2Pitch//2, stoppoint=self.m2Width//2 + self.v_enclosure, check=True)))

        self.pl = self.addGen( Wire( 'pl', 'poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=self.plPitch, width=self.plWidth, offset=self.plOffset),
                                     spg=EnclosureGrid( pitch=self.finPitch, stoppoint=self.m2Pitch//2)))

        self.fin = self.addGen( Wire( 'fin', 'fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=self.finPitch, width=self.finWidth, offset=self.finOffset),
                                      spg=CenteredGrid( pitch=self.plPitch)))

        self.active = self.addGen( Wire( 'active', 'active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=self.activePitch, width=self.activeWidth, offset=self.activeOffset),
                                         spg=SingleGrid( pitch=self.plPitch)))

        self.RVT = self.addGen( Wire( 'RVT', 'polycon', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=self.RVTPitch, width=self.RVTWidth, offset=self.RVTOffset),
                                      spg=SingleGrid( pitch=self.plPitch)))

        self.nselect = self.addGen( Region( 'nselect', 'nselect',
                                            v_grid=CenteredGrid( pitch=self.plPitch),
                                            h_grid=self.fin.clg))

        v0x_offset = self.finDummy*self.finPitch - self.fin_enclosure - self.finWidth//2 + self.finOffset + self.v0Width//2
        self.v0 = self.addGen( Via( 'v0', 'via0',
                                    h_clg=UncoloredCenterLineGrid( pitch=self.v0Pitch, width=self.v0Width, offset=v0x_offset),
                                    v_clg=self.m1.clg))

        self.v1 = self.addGen( Via( 'v1', 'via1', h_clg=self.m2.clg,  v_clg=self.m1.clg))

        self.v2 = self.addGen( Via( 'v2', 'via2', h_clg=self.m2.clg,  v_clg=self.m3.clg))


class UnitCell(CanvasNMOS):

    def unit( self, x, y, x_cells, y_cells, fin_u, gate_u):

        #####   Derived parameters   #####         
        fin = int(round(fin_u + 2*self.finDummy)) #### Total number of fins per unit cell    
        cont_no = int(round(self.activeWidth/self.v0Pitch)) ### number of V0 
        x_length = self.gate*self.plPitch
        y_length = fin * self.finPitch
        y_total = y_length*y_cells

        m1Length = self.m2Width/2 + self.v_enclosure + self.m2Pitch*((fin_u+2)//2)
        m1PCLength = self.m2Width + 2*self.v_enclosure + self.m2Pitch*((fin_u+3)//2)
        m2_tracks = int(round(y_total/self.m2Pitch)) ### Total number of M2-tracks 

        #####   This part generats locations of S/D/G   #####
        SA = []
        SB = []
        DA = []
        DB = []
        GA = []
        GB = []
        for k in range(x_cells//2):
            p = self.gateDummy - 1
            if k%2 != 0:
                p += self.gate
            lS = 2*k*self.gate + p
            lG = lS + 1
            lD = lS + gate_u
            SA.append(lS)
            GA.append(lG)
            DA.append(lD)
        for k in range(x_cells//2):
            p = self.gateDummy - 1
            if k%2 == 0:
                p += self.gate
            lS = 2*k*self.gate + p
            lG = lS + 1
            lD = lS + gate_u
            SB.append(lS)
            GB.append(lG)
            DB.append(lD)

        S = SA + SB
        D = DA + DB
        G = GA + GB

        #####   Active and RVT Layers   #####
        grid_x0 = (self.gateDummy - 1) + x*self.gate
# Try to remove self.plPitch and self.activeWidth_h
        grid_x1 = grid_x0 + self.activeWidth_h//self.plPitch

        self.addWire( self.active, 'active', y, grid_x0, grid_x1) 
        self.addWire( self.RVT,    'RVT',    y, grid_x0, grid_x1) 

        #####   Active fins   #####
        grid_x0 = x*self.gate
        grid_x1 = grid_x0 + self.gate
        for i in range(fin):  
            self.addWire( self.fin, 'fin', i+y*fin, (grid_x0, -1), (grid_x1, -1))

        #####   Gate Placement   #####
        for i in range(self.gate):
            xx = i+(x*self.gate)
            assert y_length % self.finPitch == 0
            grid_y0 = y * fin
            grid_y1 = (1+y)*fin
            self.addWire( self.pl, 'g', xx, (grid_y0, -1), (grid_y1, 1 if y == y_cells-1 else -1))
                
        #####   Nselect Placement   #####
        if x == x_cells -1 and y == y_cells -1:

            assert 2*self.finPitch == self.m2Pitch

            grid_y0 = -1
            grid_y1 = (y+1)*fin + 1

            grid_x0 = 0
            grid_x1 = (1+x)*self.gate

            self.addRegion( self.nselect, 'nselect', None, (grid_x0, -1), grid_y0, (grid_x1, -1), grid_y1)


        for i in [self.gateDummy-1, self.gateDummy + gate_u - 1]: 
            assert i < self.gate-1
            for j in range(cont_no):

                assert (fin_u + 2*self.finDummy) % 3 == 0
                assert self.activePitch % self.v0Pitch == 0

                grid_xx = i + x*self.gate
                grid_yy = j + y*((fin_u + 2*self.finDummy)*self.finPitch)//self.v0Pitch

                self.addVia( self.v0, 'v0', None, grid_xx, grid_yy)

############### M3 routing ###########################

        if y_cells > 1:
            pattern = { 0 : [(0,1), (1,0), (2,2)], 1 :  [(1,3), (2,4)]}

            for (i, adjust) in pattern[x]:
                grid_x = i+self.gateDummy + x*self.gate-1
                if y == 0:
                    grid_y0 = adjust + (self.finDummy-1)//2 - 1
                    grid_y1 = grid_y0 + (y_cells-1)*(fin//2)
                    self.addWire( self.m3, 'm3', grid_x, (grid_y0,-1), (grid_y1,1))

                grid_y = y*(m2_tracks //y_cells) + self.finDummy//2 + adjust
                self.addVia( self.v2, 'v2', grid_x, grid_y-1)


############### M2 routing ###########################

        for i in range((m2_tracks+1)):
            for (imatch, pin) in [(0, 'G'), (3, 'SB'), (1, 'SA'), (2, 'DA'), (4, 'DB')]:
                if x_cells > 1 and x == 0 and i == y*(m2_tracks //y_cells) + self.finDummy//2 + imatch:
                    assert self.m1Pitch == self.plPitch
                    grid_x0 = self.gateDummy-1
                    grid_x1 = x_cells*self.gate - 2*self.gateDummy + 2
                    self.addWire( self.m2, pin, i-1, (grid_x0, -1), (grid_x1, 1), netType = "pin")

                                                     
################# M1 routing ######################
        if x_cells - 1 == x:
            grid_y0 = y*(m2_tracks //y_cells) + self.finDummy//2 - 1
            grid_y1 = grid_y0 + (fin_u+2)//2

            for i in S + D:
                self.addWire( self.m0, 'm0', i, (y, -1), (y, 1))
                SD = 'S' if i in S else 'D'
                self.addWire( self.m1, SD, i, (grid_y0, -1), (grid_y1, 1))

            for i in G:
                self.addWire( self.m1, 'G', i, (grid_y0, -1), (grid_y1, 1))

######## Vias placement ########
        if x_cells - 1 == x:
            
            (sa,sb) = (1,3) if y % 2 == 0 else (3,1)
            (da,db) = (2,4) if y % 2 == 0 else (4,2)

            triples = [('G',G,0),('SA',SA,sa),('SB',SB,sb),('DA',DA,da),('DB',DB,db)]
            for (net,i,y_offset) in itertools.chain( *[[(net,p,q) for p in P] for (net,P,q) in triples]):
                yy = y*(m2_tracks //y_cells) + self.finDummy//2 + y_offset - 1
                self.addVia( self.v1, net, None, i, yy)
