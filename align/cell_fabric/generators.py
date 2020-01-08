
class Wire:
    def __init__( self, nm, layer, direction, *, clg, spg):
        self.nm = nm
        self.layer = layer
        self.direction = direction
        assert direction in ['v','h']
        self.clg = clg
        self.spg = spg

    def segment( self, netName, pinName, center, bIdx, eIdx, *, bS=None, eS=None):
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

    def segment( self, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1):

        rect = [self.physical_x(grid_x0), self.physical_y(grid_y0),
                self.physical_x(grid_x1), self.physical_y(grid_y1)]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        return data

class Via:
    def __init__( self, nm, layer, *, h_clg, v_clg, h_ext=1, v_ext=1):
        self.nm = nm
        self.layer = layer

        self.h_clg = h_clg
        self.v_clg = v_clg

        self.h_ext = h_ext
        self.v_ext = v_ext

    def physical_xs( self, p):
        (c,(w,_)) = self.v_clg.value( p)
        return (c-w//2,c+w//2)

    def physical_ys( self, p):
        (c,(w,_)) = self.h_clg.value( p)
        return (c-w//2,c+w//2)

    def segment( self, netName, pinName, grid_cx, grid_cy):
        (x0,x1) = self.physical_xs( grid_cx)
        (y0,y1) = self.physical_ys( grid_cy)
        rect = [ x0, y0, x1, y1]

        data = { 'netName' : netName, 'layer' : self.layer, 'rect' : rect}

        if pinName is not None:
            data['pin'] = pinName

        return data

    def center_to_metal_edge(self, direction):
        assert direction in ('h', 'v')
        return getattr(self, f'{direction}_ext')
