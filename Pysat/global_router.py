import tally
from collections import OrderedDict

class Grid:
    def __init__( self, nx, ny):
        self.nx = nx
        self.ny = ny
        self.nets = OrderedDict()
        self.layers = ['metal2','metal3']

    def addTerminal( self, net_nm, x, y):
        if net_nm not in self.nets: self.nets[net_nm] = []
        self.nets[net_nm].append( ( x, y))
    
    def idx( self, x, y):
        return self.ny*x + y

    def semantic( self):
        self.s = tally.Tally() 

        self.per_net_grid = OrderedDict()
        for (k,v) in self.nets.items():
            self.per_net_grid[k] = OrderedDict()
            for ly in self.layers:
                self.per_net_grid[k][ly] = tally.BitVec( self.s, k + '_' + ly, self.nx * self.ny)
        
        max_capacity = 1
        for x in range(self.nx):
            for y in range(self.ny):
                for ly in self.layers:
                    outs_bv = tally.BitVec( self.s, 'cap_%s_%d_%d' % (ly,x,y), max_capacity+1)
                    outs = [ outs_bv.var( i) for i in range(max_capacity+1)]
                    inps = [ self.per_net_grid[k][ly].var( self.idx(x,y)) for k in self.nets.keys()]
                    self.s.emit_tally( inps, outs)
                    self.s.emit_never( outs_bv.var( max_capacity))
                    
        self.routes = OrderedDict()

# All z routes for two terminal nets        
        for (k,v) in self.nets.items():
            assert len(v) == 2

            self.routes[k] = []

# step in x
            x0,y0 = v[0]
            x1,y1 = v[1]

            if x0 > x1:
                x0,y0,x1,y1 = x1,y1,x0,y0

            for x in range(x0,x1+1):
                r = tally.BitVar( self.s, '%s_route_x_%d' % ( k, x))
                self.routes[k].append( r)

                if x != x0: self.emitWire( k, r, "metal2", x0, y0, x, y0)
                self.emitWire( k, r, "metal3", x, y0, x, y1)
                if x != x1: self.emitWire( k, r, "metal2", x, y1, x1, y1)

# step in y
            x0,y0 = v[0]
            x1,y1 = v[1]

            if y0 > y1:
                x0,y0,x1,y1 = x1,y1,x0,y0

            for y in range(y0,y1+1):
                r = tally.BitVar( self.s, '%s_route_y_%d' % ( k, y))
                self.routes[k].append( r)

                if y != y0: self.emitWire( k, r, "metal3", x0, y0, x0, y)
                self.emitWire( k, r, "metal2", x0, y, x1, y)
                if y != y1: self.emitWire( k, r, "metal3", x1, y, x1, y1)

            self.s.emit_at_least_one( [ bv.var() for bv in self.routes[k]])


    def emitWire( self, k, r, ly, x0, y0, x1, y1):
        print( ly, x0, y0, x1, y1)

        if x0 != x1:
            assert y0 == y1
            if x0 > x1: x0,x1 = x1,x0
            for x in range( x0, x1+1):
                self.s.emit_implies( r.var(), self.per_net_grid[k][ly].var( self.idx(x,y0)))

        if y0 != y1:
            assert x0 == x1
            if y0 > y1: y0,y1 = y1,y0
            for y in range( y0, y1+1):
                self.s.emit_implies( r.var(), self.per_net_grid[k][ly].var( self.idx(x0,y)))


def test_simple():
    halfn = 50
    n = 2*halfn
    g = Grid( n, n)
    for q in range(0,halfn):
        g.addTerminal( 'a%d' % q, 0,   q)
        g.addTerminal( 'a%d' % q, n-1, q+halfn)

    g.semantic()
    g.s.solve()
    print( g.s.state)

    for (k,v) in g.routes.items():
        for bv in v:
            print( bv, bv.val())

    for (k,v) in g.per_net_grid.items():
        for (ly,bv) in v.items():
            print( k, ly)
            for y in range(g.ny-1,-1,-1): 
                tmp = [ ('1' if bv.val(g.idx(x,y)) else '0') for x in range(g.nx)]
                print( ''.join( tmp))
