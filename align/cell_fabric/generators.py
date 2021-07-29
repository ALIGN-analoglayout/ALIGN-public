
class Wire:
    def __init__( self, nm, layer, direction, *, clg, spg):
        self.nm = nm
        self.layer = layer
        self.direction = direction
        assert direction in ['v','h']
        self.clg = clg
        self.spg = spg

    def segment( self, netName, pinName, center, bIdx, eIdx, *, bS=None, eS=None, netType="drawing"):
        if bS is None: bS=self.spg
        if eS is None: eS=self.spg

        (c,(w,clr)) = self.clg.value( center)
        c0 = c - w//2
        c1 = c + w//2
        bPhys = bS.value(bIdx)[0]
        ePhys = eS.value(eIdx)[0]
        if self.direction == 'h':
            rect = [ bPhys, c0, ePhys, c1]
        else:
            rect = [ c0, bPhys, c1, ePhys]
        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        if clr is not None:
            data['color'] = clr
        
        if netType in ['drawing', 'pin', 'blockage']:
            data['netType'] = netType
        else:
            assert "Invalid net type, valid net types include drawing, pin, and blockage"
        return data

class Region:
    def __init__( self, nm, layer, *, h_grid, v_grid):
        self.nm = nm
        self.layer = layer
        self.h_grid = h_grid
        self.v_grid = v_grid

    def physical_x( self, grid_x):
        return self.v_grid.value( grid_x)[0]

    def physical_y( self, grid_y):
        return self.h_grid.value( grid_y)[0]

    def segment( self, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1, netType="drawing"):

        rect = [self.physical_x(grid_x0), self.physical_y(grid_y0),
                self.physical_x(grid_x1), self.physical_y(grid_y1)]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName
        data['netType'] = netType

        return data

class Via:
    def __init__( self, nm, layer, *, h_clg, v_clg, WidthX=None, WidthY=None, h_ext=None, v_ext=None):
        self.nm = nm
        self.layer = layer

        self.h_clg = h_clg
        self.v_clg = v_clg

        if WidthX is not None:
            self.WidthX = WidthX
        elif self.v_clg is not None:
            self.WidthX = self.v_clg.grid[0][1][0]
        else:
            self.WidthX = 2

        if WidthY is not None:
            self.WidthY = WidthY
        elif self.h_clg is not None:
            self.WidthY = self.h_clg.grid[0][1][0]
        else:
            self.WidthY = 2

        self.h_ext = h_ext if h_ext is not None else (self.WidthX // 2)
        self.v_ext = v_ext if v_ext is not None else (self.WidthY // 2)

    def physical_xs( self, p):
        c = self.v_clg.value( p)[0]
        return (c-self.WidthX//2,c+self.WidthX//2)

    def physical_ys( self, p):
        c = self.h_clg.value( p)[0]
        return (c-self.WidthY//2,c+self.WidthY//2)

    def segment( self, netName, pinName, grid_cx, grid_cy, netType="drawing"):
        (x0,x1) = self.physical_xs( grid_cx)
        (y0,y1) = self.physical_ys( grid_cy)
        rect = [ x0, y0, x1, y1]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName
        data['netType'] = netType

        return data

    def center_to_metal_edge(self, direction):
        assert direction in ('h', 'v')
        return getattr(self, f'{direction}_ext')
