
import json
import transformation
import argparse

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
            rect = [ self.value(bIdx), c0, self.value(eIdx), c1]
        else:
            rect = [ c0, self.value(bIdx), c1, self.value(eIdx)]
        return { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}


############ Via class ##################

class Via:
    def __init__( self, nm, layer, *, widthx, widthy, pitchx, pitchy, offsetx=0, offsety=0):
        self.nm = nm
        self.layer = layer           
        self.widthx = widthx
        self.widthy = widthy
        self.pitchx = pitchx
        self.pitchy = pitchy
        self.offsetx = offsetx
        self.offsety = offsety
        assert pitchx > widthx > 0
        assert pitchy > widthy > 0
        

    def segment( self, netName, cx, cy1):
        if type(cy1) is tuple:
            cy = cy1[1] + cy1[0]//self.pitchy
        else:
            cy = cy1
        cx0 = cx*self.pitchx + self.offsetx
        cy0 = cy*self.pitchy + self.offsety
        c0 = cx0 - self.widthx//2
        c1 = cx0 + self.widthx//2
        c2 = cy0 - self.widthy//2
        c3 = cy0 + self.widthy//2        
        rect = [ c0, c2, c1, c3]        
        return { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

    
class Canvas():
    def computeBbox( self):
        self.bbox = transformation.Rect(None,None,None,None)
        for term in self.terminals:
            r = transformation.Rect( *term['rect'])
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury
   
    
    
    def __init__( self, fin, finDummy, gate, gateDummy):
        self.terminals = []
        with open('./FinFET_Mock_PDK_FEOL_Abstraction.json') as f:
            Feol = json.load(f)

        plWidth = Feol["plWidth"]
        plPitch  = Feol["plPitch"]
        finWidth = Feol["finWidth"]
        finPitch = Feol["finPitch"]
        m1Width = Feol["m1Width"]
        m1Pitch  = Feol["m1Pitch"]
        m2Pitch  = Feol["m2Pitch"]
        m2Width = Feol["m2Width"]
        m3Pitch  = Feol["m3Pitch"]
        m3Width = Feol["m3Width"]                 
        pcWidth = Feol["pcWidth"]                        
        dcWidth = Feol["dcWidth"]
        tbWidth = Feol["tbWidth"] 
        v0Width = Feol["v0Width"]
        v0Pitch = Feol["v0Pitch"]
        v1Width = Feol["v1Width"]  
        v2Width = Feol["v2Width"]  
        v0_enclosure = Feol["v0_enclosure"]   
        v_enclosure = Feol["v_enclosure"]
        active_enclosure = Feol["active_enclosure"]

        assert v0Pitch < 2*m2Pitch                 


######### Derived parameters ######################
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy        
        # Must be a multiple of 2
        assert self.finsPerUnitCell % 2 == 0
        assert finDummy % 2 == 0
        assert gateDummy > 0
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell*m2Pitch
        unitCellLength = self.gatesPerUnitCell*plPitch
        dcPitch  = 2*m1Pitch
        m2Offset = -m2Pitch//2
        plOffset = plPitch//2 
        finOffset = 0                
        pcPitch  = self.unitCellHeight//2
        #activeWidth1 = finPitch*fin_u
        activeWidth = finPitch*fin
        #activeWidth_h = ((gate_u-1)* self.plPitch) + (self.plActive_s * 2) + self.plWidth
        activeOffset = activeWidth/2 + finDummy*finPitch - finPitch/2 + finOffset
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*active_enclosure
        RVTOffset = RVTWidth/2 + finDummy*finPitch - finPitch/2 - active_enclosure + finOffset
        self.cont = activeWidth//(2*m2Pitch)
################################################################################################

        stoppoint = unitCellLength
        self.nd = StopPointGrid( 'fin', 'fin', 'h', width=finWidth, pitch=finPitch)
        self.nd.addGridPoint( 0,                 True)
        self.nd.addGridPoint( stoppoint,           True)
         
        stoppoint = (gateDummy-1)*plPitch + plOffset
        self.active = StopPointGrid( 'active', 'active', 'h', width=activeWidth, pitch=activePitch, offset=activeOffset)
        self.active.addGridPoint( stoppoint,         True)
        self.active.addGridPoint( unitCellLength-stoppoint,          True)
        self.active.addGridPoint( unitCellLength,          False)
 
        self.RVT = StopPointGrid( 'RVT', 'polycon', 'h', width=RVTWidth, pitch=activePitch, offset=RVTOffset)
        self.RVT.addGridPoint( stoppoint,         True)
        self.RVT.addGridPoint( unitCellLength - stoppoint,          True)
        self.RVT.addGridPoint( unitCellLength,          False)
        

        stoppoint = plOffset - plWidth//2
        self.pc = StopPointGrid( 'pc', 'polycon', 'h', width=pcWidth, pitch=pcPitch)
        self.pc.addGridPoint( 0,                 False)
        self.pc.addGridPoint( stoppoint,         True)
        self.pc.addGridPoint( dcPitch//2,        False)
        self.pc.addGridPoint( dcPitch - stoppoint, True)
        self.pc.addGridPoint( dcPitch,           False)

        stoppoint = m2Pitch + m2Offset - m2Width//2 - v_enclosure
        self.m1 = StopPointGrid( 'm1', 'M1', 'v', width=m1Width, pitch=m1Pitch)
        self.m1.addGridPoint( 0,                        False)
        self.m1.addGridPoint( stoppoint,                True)
        self.m1.addGridPoint( self.unitCellHeight//2,        False)
        self.m1.addGridPoint( self.unitCellHeight - stoppoint - m2Pitch, True)
        self.m1.addGridPoint( self.unitCellHeight,           False)
        
        
        self.m3 = StopPointGrid( 'm3', 'M3', 'v', width=m3Width, pitch=m3Pitch)
        self.m3.addGridPoint( 0,                        True)
        self.m3.addGridPoint( stoppoint,                True)
        self.m3.addGridPoint( self.unitCellHeight - stoppoint - m2Pitch, True)
        self.m3.addGridPoint( self.unitCellHeight,           True)

        stoppoint = gateDummy*m1Pitch - m1Width//2 - v_enclosure
        self.m2 = StopPointGrid( 'm2', 'M2', 'h', width=m2Width, pitch=m2Pitch, offset=m2Offset)
        self.m2.addGridPoint( 0,                 True)
        self.m2.addGridPoint( stoppoint,         True)
        self.m2.addGridPoint( unitCellLength - stoppoint,         True)
        self.m2.addGridPoint( unitCellLength,           True)
        

        stoppoint = -m2Pitch//2
        self.pl = StopPointGrid( 'pl', 'poly', 'v', width=plWidth, pitch=plPitch, offset=plOffset)
        self.pl.addGridPoint( stoppoint,                           True)
        self.pl.addGridPoint( self.unitCellHeight,              True)

        stoppoint = -m2Pitch//2
        self.tb = StopPointGrid( 'tb', 'poly', 'v', width=tbWidth, pitch=plPitch, offset=plOffset)
        self.tb.addGridPoint( stoppoint,                           True)
        self.tb.addGridPoint( self.unitCellHeight,              True)

        self.dc = StopPointGrid( 'dc', 'diffcon', 'v', width=dcWidth, pitch=dcPitch)
        self.dc.addGridPoint( 0,                           False)
        self.dc.addGridPoint( stoppoint,                   True)
        self.dc.addGridPoint( self.unitCellHeight//2 - stoppoint, True)
        self.dc.addGridPoint( self.unitCellHeight//2,           False)
        self.dc.addGridPoint( self.unitCellHeight//2 + stoppoint, True)
        self.dc.addGridPoint( self.unitCellHeight - stoppoint,    True)
        self.dc.addGridPoint( self.unitCellHeight,              False)

        self.v0 = Via( 'v0', 'via0', widthx=v0Width, widthy=v0Width, pitchx=m1Pitch, pitchy=2*m2Pitch, offsetx=0, offsety=m2Offset + (1+finDummy//2)*m2Pitch)

        self.v1 = Via( 'v1', 'via1', widthx=v1Width, widthy=v1Width, pitchx=m1Pitch, pitchy=m2Pitch, offsetx=0, offsety=m2Offset)

        self.v2 = Via( 'v2', 'via2', widthx=v2Width, widthy=v2Width, pitchx=m1Pitch, pitchy=m2Pitch, offsetx=0, offsety=m2Offset)
        
    def addSegment( self, grid, netName, c, bIdx, eIdx):
        def f( idx):
            if type(idx) is tuple:
                return idx[1] + grid.n*idx[0]
            else:
                return idx
        segment = grid.segment( netName, c, f(bIdx), f(eIdx))
        self.terminals.append( segment)
        return segment

    def addViasegment( self, grid, netName, cx, cy):
        def f ( idx):
            if type(idx) is tuple:
                return (idx[0]*self.unitCellHeight, idx[1])
            else:
                return idx
        segment = grid.segment( netName, cx, f(cy))
        self.terminals.append( segment)
        return segment
    

        
    def pcSegment( self, netName, x0, x1, y): return self.addSegment( self.pc, netName, y, x0, x1)
    def m1Segment( self, netName, x, y0, y1): return self.addSegment( self.m1, netName, x, y0, y1)
    def m2Segment( self, netName, x0, x1, y): return self.addSegment( self.m2, netName, y, x0, x1)
    def m3Segment( self, netName, x, y0, y1): return self.addSegment( self.m3, netName, x, y0, y1)
    def plSegment( self, netName, x, y0, y1): return self.addSegment( self.pl, netName, x, y0, y1)
    def tbSegment( self, netName, x, y0, y1): return self.addSegment( self.tb, netName, x, y0, y1)
    def dcSegment( self, netName, x, y0, y1): return self.addSegment( self.dc, netName, x, y0, y1)
    def ndSegment( self, netName, x0, x1, y): return self.addSegment( self.nd, netName, y, x0, x1)
    def activeSegment( self, netName, x0, x1, y): return self.addSegment( self.active, netName, y, x0, x1)
    def RVTSegment( self, netName, x0, x1, y): return self.addSegment( self.RVT, netName, y, x0, x1)
    def v0Segment( self, netName, x0, y0): return self.addViasegment( self.v0, netName, x0, y0)
    def v1Segment( self, netName, x0, y0): return self.addViasegment( self.v1, netName, x0, y0)
    def v2Segment( self, netName, x0, y0): return self.addViasegment( self.v2, netName, x0, y0)

    def nunit( self, x, y, x_cells, y_cells, fin, finDummy, gate, gateDummy):
                 
        self.activeSegment('active', (x,0), (x,1), y)
        self.RVTSegment('RVT', (x,0), (x,1), y)
 
        for i in range(self.finsPerUnitCell):
            self.ndSegment( 'fin', x, x+1, self.finsPerUnitCell*y+i)   

        gu = self.gatesPerUnitCell                   
      
        for i in range(gu):        
            self.plSegment( 'g', gu*x+i,   (y,0), (y,1))
            self.tbSegment( 'tb', gu*x+i,   (y,0), (y,1))   
                         
        #assert self.m2PerUnitCell % 2 == 1
        h = self.m2PerUnitCell
        (p) = (1) if x == 0 else (-1)

        for i in range(1,h):                        
            self.m2Segment( 'm2', (x,p), (x,2), h*y+i)

        self.m2Segment( 'm2', (x,0), (x,3), h*(y+1)) ### Power line
        if y == 0:
            self.m2Segment( 'm2', (x,0), (x,3), 0) #### Ground line
        
##### Primitive cell dependent Via placement #####
        S = []
        D = []
        G = []
        for k in range(x_cells):
            lS = k*gu + gateDummy
            lG = lS+1
            lD = lS + gate
            S.append(lS)
            G.append(lG)
            D.append(lD)

        (p) = (1) if y == 0 else (-1)
        
        if x == 0:
            for i in S:
                self.m1Segment( 's', i, (y, 1), (y, 3))
                self.v1Segment('via1', i, (y, 2))
                for j in range(self.cont):
                    self.v0Segment('via0', i, (y, j))
            for i in D:
                self.m1Segment( 'd', i, (y, 1), (y, 3))
                self.v1Segment('via1', i, (y, 3))
                for j in range(self.cont):
                    self.v0Segment('via0', i, (y, j))
            for i in G:
                self.m1Segment( 'g', i, (y, 1), (y, 3))
                self.v1Segment('via1', i, (y, 1))
            for i in range(3):
                self.m3Segment( 'm3', i+gateDummy, (y,p), (y,2))
                self.v2Segment('via2', i+gateDummy, (y, 1+i))
                
                                
if __name__ == "__main__":
    
    parser = argparse.ArgumentParser( description="Inputs for Cell Generation")
    parser.add_argument( "-b", "--block_name", type=str, required=True)
    parser.add_argument( "-n", "--nfin", type=int, required=True)
    parser.add_argument( "-X", "--Xcells", type=int, required=True)
    parser.add_argument( "-Y", "--Ycells", type=int, required=True)
    args = parser.parse_args()
    fin_u = args.nfin
    x_cells = args.Xcells
    y_cells = args.Ycells
    #gate_u = int(sys.argv[4])
    #gate_u = 4
    gate = 2
    fin = 2*((fin_u+1)//2)
    gateDummy = 2 ### Total Dummy gates per unit cell 2*gateDummy
    finDummy = 2  ### Total Dummy fins per unit cell 2*finDummy                     
    c = Canvas(fin, finDummy, gate, gateDummy)
    
    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        c.nunit( x, y, x_cells, y_cells, fin, finDummy, gate, gateDummy)
    c.computeBbox()   
    with open( "./Viewer/INPUT/mydesign_dr_globalrouting.json", "wt") as fp:
        data = { 'bbox' : c.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : c.terminals}
        fp.write( json.dumps( data, indent=2) + '\n')
    #gen_json_gds.json_gds("./Viewer/INPUT/mydesign_dr_globalrouting.json",args.block_name)
    #cell_pin = ["S", "G", "D"]
    #gen_lef.json_lef(args.block_name + '.json',args.block_name,cell_pin)
    #system('python3 setup.py build_ext --inplace')
    #system('python3 gen_gds.py -j %s.json -n %s -e MTI' % (args.block_name,args.block_name))
