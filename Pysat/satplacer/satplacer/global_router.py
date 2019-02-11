import tally
from collections import OrderedDict
import json

from cktgen.transformation import Rect, Transformation, Tech

class GR:
  def __init__( self, netName=None, layer=None, width=None, rect=None):
    self.netName = netName
    self.layer = layer
    self.width = width
    self.rect = rect

def encode_GR( tech, obj):

  #
  # Very broken ---
  #   remove *2 and //2 later
  #


  if isinstance(obj, GR):
# Convert global route coords to physical coords
    if obj.layer in tech.verticalMetals:
      assert obj.rect.llx == obj.rect.urx
      xc = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.llx + tech.halfXGRGrid)
      llx = xc - obj.width//2
      urx = xc + obj.width//2
      lly = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.lly + tech.halfYGRGrid - (tech.halfYGRGrid - 1))
      ury = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.ury + tech.halfYGRGrid + (tech.halfYGRGrid - 1))
    elif obj.layer in tech.horizontalMetals:
      assert obj.rect.lly == obj.rect.ury
      yc = tech.pitchDG*(tech.halfYGRGrid*2*obj.rect.lly + tech.halfYGRGrid)
      lly = yc - obj.width//2
      ury = yc + obj.width//2
      llx = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.llx + tech.halfXGRGrid - (tech.halfXGRGrid - 1))
      urx = tech.pitchPoly*(tech.halfXGRGrid*2*obj.rect.urx + tech.halfXGRGrid + (tech.halfXGRGrid - 1))
    else:
      raise RuntimeError(repr(obj) + ("is not horizontal nor vertical (%d,%d,%d,%d)." % (obj.rect.llx,obj.rect.lly,obj.rect.urx,obj.rect.ury)))

    return { "netName" : obj.netName, "layer" : obj.layer, "width" : obj.width, "rect" : [llx, lly, urx, ury]}
  else:
    raise TypeError(repr(obj) + " is not JSON serializable.")

class Grid:
    def __init__( self, nx, ny, gridFactor):
        self.nx = nx
        self.ny = ny
        self.gridFactor = gridFactor
        self.nets = OrderedDict()
        self.layers = ['metal2','metal3']
        self.routes = OrderedDict()
        print( "Grid size:", self.nx, self.ny)

    def dumpJSON( self, fp, tech):
      wires = []
      for (k,v) in self.wires.items():
        for (ly,grs) in v.items():
          for gr in grs:
            wires.append( { "layer": gr.layer, "net_name": gr.netName, "width": gr.width, "rect": gr.rect.toList()})

      data = { "wires": wires}
      fp.write( json.dumps( data, indent=2) + "\n") 

    def addTerminal( self, net_nm, x, y):
        if net_nm not in self.nets: self.nets[net_nm] = set()
        self.nets[net_nm].add( ( x, y))
    
    def idx( self, x, y):
        return self.ny*x + y

    def allRasterPoints( self):
      for x in range(self.nx):
        for y in range(self.ny):
          for (k,v) in self.per_net_grid.items():
            for (ly,bv) in v.items():
              yield x,y,k,ly,bv

    def cleanAntennas( self):
      
      print( "Phase 1: cleanAntennas: force all routing decision to remain.")
      for (k,v) in self.routes.items():
        for r in v:
          if r.val() is True:
            self.s.emit_always( r.var())
          elif r.val() is False:
            self.s.emit_never( r.var())
      self.s.solve()
      assert self.s.state == 'SAT'

      print( "Phase 2: cleanAntennas: force all empty sites to remain empty.")
      for (x,y,k,ly,bv) in self.allRasterPoints():
        if bv.val( self.idx(x,y)) is False:
          self.s.emit_never( bv.var( self.idx(x,y)))
      self.s.solve()
      assert self.s.state == 'SAT'

      print( "Phase 3: cleanAntennas: one by one, check if a site can be made empty, then force it to remain empty.")
      for (x,y,k,ly,bv) in self.allRasterPoints():
        if bv.val( self.idx(x,y)) is True:
          self.s.solve( assumptions=[-bv.var( self.idx(x,y))])
          if self.s.state == 'SAT':
            print( "Removing antenna from %s %s %d %d" % (k,ly,x,y))
            self.s.emit_never( bv.var( self.idx(x,y)))                           
      self.s.solve()
      assert self.s.state == 'SAT'

    def genMaxCapacityConstraints( self, max_capacity):
      self.max_capacity_constraints = OrderedDict()
      for ly in self.layers:
        self.max_capacity_constraints[ly] = OrderedDict()
        for x in range(self.nx):
          for y in range(self.ny):
            outs_bv = tally.BitVec( self.s, 'cap_%s_%d_%d' % (ly,x,y), max_capacity+1)

            self.max_capacity_constraints[ly][(x,y)] = outs_bv

            outs = [ outs_bv.var( i) for i in range(max_capacity+1)]
            inps = [ self.per_net_grid[k][ly].var( self.idx(x,y)) for k in self.nets.keys()]
            self.s.emit_tally( inps, outs)
            self.s.emit_never( outs_bv.var( max_capacity))

    def genDifferentNetMaxCapacityConstraints( self, max_capacity):
          for x in range(self.nx):
            for y in range(self.ny):
              for (l,ll) in ( (l, ll) for l in self.layers for ll in self.layers if l != ll):
                for k in self.per_net_grid.keys():
                  inps = [ self.per_net_grid[k ][l ].var( self.idx(x,y))] + \
                         [ self.per_net_grid[kk][ll].var( self.idx(x,y)) for kk in self.per_net_grid.keys() if k != kk]
                  outs_bv = tally.BitVec( self.s, 'cap2_%s_%s_%s_%d_%d' % (l,ll,k,x,y), max_capacity+1)
                  outs = [ outs_bv.var( i) for i in range( max_capacity+1)]
                  self.s.emit_tally( inps, outs)
                  self.s.emit_never( outs_bv.var( max_capacity))

    def genRoutes( self):
        hly = "metal2"
        vly = "metal3"

        for (k,v) in self.nets.items():
            v = list(set(v))
            if len(v) < 2: continue

            self.routes[k] = []

            for xy in v:
              assert 0 <= xy[0] < self.nx, ( k, v, self.nx, self.ny)
              assert 0 <= xy[1] < self.ny, ( k, v, self.nx, self.ny)


            minx = min( xy[0] for xy in v)
            maxx = max( xy[0] for xy in v)
            miny = min( xy[1] for xy in v)
            maxy = max( xy[1] for xy in v)

            # step in x
            if minx < maxx:
              for x in range(minx,maxx+1):
                r = tally.BitVar( self.s, '%s_route_x_%d' % ( k, x))
                self.routes[k].append( r)

                self.emitWire( k, r, vly, x, miny, x, maxy)  # trunk

                for (xx,yy) in v:  # stubs
                  if x != xx:
                    self.emitWire( k, r, hly, min(x,xx), yy, max(x,xx),  yy)

            if miny < maxy:
              for y in range(miny,maxy+1):
                r = tally.BitVar( self.s, '%s_route_y_%d' % ( k, y))
                self.routes[k].append( r)

                self.emitWire( k, r, hly, minx, y, maxx, y)  # trunk

                for (xx,yy) in v:  # stubs
                  if y != yy:
                    self.emitWire( k, r, vly, xx, min(y,yy), xx, max(y,yy))

            if self.routes[k]:
              self.s.emit_at_least_one( [ bv.var() for bv in self.routes[k]])


    def genSymmetricRoutes( self, n0, n1):
        hly = "metal2"
        vly = "metal3"

        (k0,v0) = n0
        (k1,v1) = n1

        assert len(v0) == 2
        assert len(v1) == 2

        # check assumed mirroring about a vertical line

        v0 = list(v0)
        v1 = list(v1)

        if v0[0][0] > v0[1][0]:
          v0[0],v0[1] = v0[1],v0[0]

        if v1[0][0] > v1[1][0]:
          v1[0],v1[1] = v1[1],v1[0]

        # y coords the same
        assert v0[0][1] == v1[1][1] 
        assert v0[1][1] == v1[0][1] 

        # x coords flip
        xdist = v1[1][0] - v0[0][0]
        assert v0[0][0] == xdist - v1[1][0]
        assert v0[1][0] == xdist - v1[0][0]

        def allStepX( k, v, kk, vv):
          x0,y0 = v[0]
          x1,y1 = v[1]

          if x0 > x1:
            x0,y0,x1,y1 = x1,y1,x0,y0

          for x in range(x0,x1+1):
            r = tally.BitVar( self.s, '%s_%s_symmetric_route_x_%d' % ( k, kk, x))
            self.routes[k].append( r)

            if x != x0: self.emitWire( k, r, hly, x0, y0, x,  y0)
            self.emitWire(             k, r, vly, x,  y0, x,  y1)
            if x != x1: self.emitWire( k, r, hly, x,  y1, x1, y1)

            if x != x0: self.emitWire( kk, r, hly, xdist - x,  y0, xdist - x0, y0)
            self.emitWire(             kk, r, vly, xdist - x,  y0, xdist - x,  y1)
            if x != x1: self.emitWire( kk, r, hly, xdist - x1, y1, xdist - x,  y1)

        def allStepY( k, v, kk, vv):
          x0,y0 = v[0]
          x1,y1 = v[1]

          if y0 > y1:
            x0,y0,x1,y1 = x1,y1,x0,y0

          for y in range(y0,y1+1):
            r = tally.BitVar( self.s, '%s_%s_symmetric_route_y_%d' % ( k, kk, y))
            self.routes[k].append( r)

            if y != y0: self.emitWire( k, r, vly, x0, y0, x0, y)
            self.emitWire(             k, r, hly, x0, y,  x1, y)
            if y != y1: self.emitWire( k, r, vly, x1, y,  x1, y1)

            if y != y0: self.emitWire( kk, r, vly, xdist - x0, y0, xdist - x0, y)
            self.emitWire(             kk, r, hly, xdist - x1, y,  xdist - x0, y)
            if y != y1: self.emitWire( kk, r, vly, xdist - x1, y,  xdist - x1, y1)

        self.routes[k0] = []

        allStepX( k0, v0, k1, v1)
        allStepY( k0, v0, k1, v1)
        self.s.emit_exactly_one( [ bv.var() for bv in self.routes[k0]])


    def semantic( self, max_capacity=1, different_net_max_capacity=None):
        self.s = tally.Tally() 

        self.per_net_grid = OrderedDict()
        for k in list(self.nets.keys()) + ['!kor']:
            self.per_net_grid[k] = OrderedDict()
            for ly in self.layers:
                self.per_net_grid[k][ly] = tally.BitVec( self.s, k + '_' + ly, self.nx * self.ny)
        
        self.genMaxCapacityConstraints( max_capacity=max_capacity)
        if different_net_max_capacity is not None:
          self.genDifferentNetMaxCapacityConstraints( different_net_max_capacity)

        self.genRoutes()

    def semanticSymmetric( self, max_capacity=1, different_net_max_capacity=None):
        self.s = tally.Tally() 

        self.per_net_grid = OrderedDict()
        for k in list(self.nets.keys()) + ['!kor']:
            self.per_net_grid[k] = OrderedDict()
            for ly in self.layers:
                self.per_net_grid[k][ly] = tally.BitVec( self.s, k + '_' + ly, self.nx * self.ny)
        
        self.genMaxCapacityConstraints( max_capacity=max_capacity)
        if different_net_max_capacity is not None:
          self.genDifferentNetMaxCapacityConstraints( different_net_max_capacity)

        items = list(self.nets.items())
        assert len(items) == 2
        self.genSymmetricRoutes( items[0], items[1])

    def emitWire( self, k, r, ly, x0, y0, x1, y1):
        print( "Call emitWire", k, ly, x0, x0, x1, y1)

        assert 0 <= x0 < self.nx, (x0,y0,x1,y1,self.nx,self.ny)
        assert 0 <= x1 < self.nx, (x0,y0,x1,y1,self.nx,self.ny)
        assert 0 <= y0 < self.ny, (x0,y0,x1,y1,self.nx,self.ny)
        assert 0 <= y1 < self.ny, (x0,y0,x1,y1,self.nx,self.ny)

        if x0 != x1:
            assert y0 == y1
            if x0 > x1: x0,x1 = x1,x0
            for x in range( x0, x1+1):
              print( k, x, y0, y1)
              self.s.emit_implies( r.var(), self.per_net_grid[k][ly].var( self.idx(x,y0)))

        if y0 != y1:
            assert x0 == x1
            if y0 > y1: y0,y1 = y1,y0
            for y in range( y0, y1+1):
              self.s.emit_implies( r.var(), self.per_net_grid[k][ly].var( self.idx(x0,y)))


    def print_routes( self):
        for (k,v) in self.routes.items():
            for bv in v:
                print( bv, bv.val())

    def print_rasters( self):
        for (k,v) in self.per_net_grid.items():
            for (ly,bv) in v.items():
                print( k, ly)
                for y in range(self.ny-1,-1,-1): 
                    print( ''.join( [ ('1' if bv.val(self.idx(x,y)) else '0') for x in range(self.nx)]))

    def genWires( self):
        horizontalMetals = ['metal2']
        verticalMetals   = ['metal3']
        self.wires = OrderedDict()
        for (k,v) in self.per_net_grid.items():
            self.wires[k] = {}
            for (ly,bv) in v.items():
                if ly in horizontalMetals:
                    for y in range(self.ny):
                        x0,x1 = None,None
                        for x in range(self.nx):
                            filled = bv.val(self.idx(x,y))
                            if filled:
                                if x0 is None: x0 = x
                                x1 = x
                            if filled and x == self.nx-1 or not filled and x1 is not None:
                                if ly not in self.wires[k]: self.wires[k][ly] = [] 
                                self.wires[k][ly].append( GR( k, ly, 400, Rect( x0, y, x1, y)))
                                x0,x1 = None,None

                if ly in verticalMetals:
                    for x in range(self.nx):
                        y0,y1 = None,None
                        for y in range(self.ny):
                            filled = bv.val(self.idx(x,y))
                            if filled:
                                if y0 is None: y0 = y
                                y1 = y
                            if filled and y == self.ny-1 or not filled and y1 is not None:
                                if ly not in self.wires[k]: self.wires[k][ly] = [] 
                                self.wires[k][ly].append( GR( k, ly, 400, Rect( x, y0, x, y1)))
                                y0,y1 = None,None

    def write_globalrouting_json( self, fp, tech, placer_results=None):
        grs = []
        terminals = []

        hack = 1 # gridFactor == 4

        if placer_results is not None:
          globalScale = Transformation( 0, 0, hack*tech.halfXADTGrid*tech.pitchPoly, hack*tech.halfYADTGrid*tech.pitchDG)
          b = globalScale.hitRect( Rect( *placer_results['bbox'])).canonical()
          terminals.append( { "netName" : placer_results['nm'], "layer" : "diearea", "rect" : b.toList()})

          print( "placer_results bbox:", b.toList())

          leaves_map = { leaf['template_name'] : leaf for leaf in placer_results['leaves']}

          for inst in placer_results['instances']:
            leaf = leaves_map[inst['template_name']]
            tr = inst['transformation']
            trans = Transformation( tr['oX'], tr['oY'], tr['sX'], tr['sY'])
            r = globalScale.hitRect( trans.hitRect( Rect( *leaf['bbox'])).canonical())

            nm = placer_results['nm'] + '/' + inst['instance_name'] + ':' + inst['template_name']

            print( nm, r)

            terminals.append( { "netName" : nm, "layer" : "cellarea", "rect" : r.toList()})

          for term in placer_results['terminals']:
            nm = term['net_name'] + ':' + term['hier_name']
            b = globalScale.hitRect( Rect( *term['rect'])).canonical()
            b.llx -= 200
            b.urx += 200
            b.lly += 360
            b.ury -= 360
            terminals.append( { "netName" : nm, "layer" : term['layer'], "rect" : b.toList()})

        for (k,v) in self.wires.items():
          for (ly, vv) in v.items():
            for gr in vv:
              terminals.append(gr)

        # halfXGRGrid should be 2
        # hack = 1 works if gridFactor is 2
        # what should hack be if gridFactor is 4
        hack = self.gridFactor // 2

        grGrid = []
        globalScale = Transformation( 0, 0, hack*tech.halfXGRGrid*tech.pitchPoly, hack*tech.halfYGRGrid*tech.pitchDG)
        self.bbox = globalScale.hitRect( Rect( 0, 0, self.nx, self.ny))
        for x in range( self.nx):
          for y in range( self.ny):
            r = globalScale.hitRect( Rect( x, y, x+1, y+1))
            print( "global route:", x, y, r)
            grGrid.append( r.toList())

        data = { "bbox" : [self.bbox.llx, self.bbox.lly, self.bbox.urx, self.bbox.ury], "globalRoutes" : grs, "globalRouteGrid" : grGrid, "terminals" : terminals}

        print( 'Grid bbox:', data['bbox'])
        fp.write( json.dumps( data, indent=2, default=lambda x: encode_GR(tech,x)) + "\n")


def ex_river_routing( max_capacity=1, different_net_max_capacity=1):
    halfn = 10
    n = 2*halfn
    g = Grid( n, n)
    for q in range(0,halfn):
        g.addTerminal( 'a%d' % q, 0,   q)
        g.addTerminal( 'a%d' % q, n-1, q+halfn)

    g.semantic( max_capacity, different_net_max_capacity)
    g.s.solve()
    assert g.s.state == 'SAT'

    g.cleanAntennas()

    g.print_routes()
    g.print_rasters()
    g.genWires()

    return g

def ex_symmetric( max_capacity=1, different_net_max_capacity=1):
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( max_capacity, different_net_max_capacity)

    for ly in g.layers:
      pass
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(5,3)))

    g.s.solve()
    assert g.s.state == 'SAT'

    g.cleanAntennas()

    g.print_routes()
    g.print_rasters()
    g.genWires()

    return g

def test_symmetric_sat_3():
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( 1, 1)

    for ly in ["metal2"]:
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,0)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
#      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,3)))

    g.s.solve()
    assert g.s.state == 'SAT'

def test_symmetric_sat_2():
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( 1, 1)

    for ly in ["metal2"]:
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,0)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
#      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,3)))

    g.s.solve()
    assert g.s.state == 'SAT'

def test_symmetric_sat_1():
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( 1, 1)

    for ly in ["metal2"]:
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,0)))
#      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,3)))

    g.s.solve()
    assert g.s.state == 'SAT'

def test_symmetric_sat_0():
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( 1, 1)

    for ly in ["metal2"]:
#      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,0)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,3)))

    g.s.solve()
    assert g.s.state == 'SAT'

def test_symmetric_unsat():
    g = Grid( 6, 4)
    g.addTerminal( 'a', 0, 0)
    g.addTerminal( 'a', 2, 3)
    g.addTerminal( 'b', 3, 3)
    g.addTerminal( 'b', 5, 0)

    g.semanticSymmetric( 1, 1)

    for ly in ["metal2"]:
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,0)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,1)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(1,2)))
      g.s.emit_always( g.per_net_grid['!kor'][ly].var( g.idx(5,3)))

    g.s.solve()
    assert g.s.state == 'UNSAT'


import translate

def aux_from_json( tag, gridFactor=4):
  with open( '%s_placer_out.json' % tag, 'rt') as fp:
    placer_results = json.load( fp)

  # scales y and adjusts x
  placer_results = translate.translatePlacerResults( placer_results)

  [_,_,nx,ny] = placer_results['bbox']
  print( "nx,ny:", nx, ny)

  print( 'BBOX', placer_results['bbox'])

  # the global router grid is twice the placer (ADT) grid
  def tr( p):
    x,y = p
    return x//gridFactor, y//gridFactor

#
# nx,ny: 26,8 => 13,4 (gridFactor=2)
# nx,ny: 26,8 =>  7,2 (gridFactor=4)
#
#
  g = Grid( (nx+gridFactor-1) // gridFactor, (ny+gridFactor-1) // gridFactor, gridFactor)

  print( 'Grid size', g.nx, g.ny)

  for term in placer_results['terminals']:
    x0,y0 = tr(tuple(term['rect'][:2]))
    x1,y1 = tr(tuple(term['rect'][2:]))

    print( term['rect'])
    print( term['net_name'], x0, y0, x1, y1)

    assert x0 == x1
    x = (x0 + x1)//2
    y = (y0 + y1)//2

    assert x <= g.nx, (x,g.nx)

    if x == g.nx: x -= 1
    g.addTerminal( term['net_name'], x, y)

  max_capacity=7
  g.semantic( max_capacity=max_capacity)
  g.s.solve()
  assert g.s.state == 'SAT'

  all_cap_bvs = OrderedDict()
  for (ly,v) in g.max_capacity_constraints.items():
    count = 0
    all_bits = []
    for ((x,y),vv) in v.items():
      count += sum( (1 if vv.val( i) is True else 0) for i in range(max_capacity+1))
      all_bits += [vv.var( i) for i in range(max_capacity)]
    print( "count:", count)

    all_cap_bvs[ly] = tally.BitVec( g.s, 'all_cap_%s' % ly, count+1)
    g.s.emit_tally( all_bits, [all_cap_bvs[ly].var( i) for i in range(count+1)])

    
  for (ly,v) in all_cap_bvs.items():
    for lim in range( v.n-1, -1, -1):
      print( "Trying to do with <", lim, "in layer", ly)
      g.s.solve( [-v.var( lim)])
      if g.s.state == 'UNSAT':
        print( "Can't do with <", lim, "in layer", ly)
        if lim < v.n-1:
          g.s.emit_never( v.var( lim+1))
        break
      else:
        print( "Can do with <", lim, "in layer", ly)
          
  g.cleanAntennas()

  g.print_routes()
  g.print_rasters()
  g.genWires()

  with open( "mydesign_dr_globalrouting.json", "wt") as fp:
    tech = Tech()
    g.write_globalrouting_json( fp, tech, placer_results)

  with open( "%s_global_router_out.json" % tag, "wt") as fp:
    tech = Tech()      
    g.dumpJSON( fp, tech)

def ex_backward_xy():
    halfn = 2
    n = 2*halfn
    g = Grid( n, n)
    for q in range(0,halfn):
        g.addTerminal( 'a%d' % q, n-1, q+halfn)
        g.addTerminal( 'a%d' % q, 0,   q)

    g.semantic( max_capacity=1)
    g.s.solve()
    assert g.s.state == 'SAT'

def ex_write_globalrouting_json( g):
    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)
  

def test_symmetric_1_1():
  ex_symmetric( max_capacity=1, different_net_max_capacity=1)

def test_symmetric_1_None():
  ex_symmetric( max_capacity=1, different_net_max_capacity=None)

def test_river_routing_1_None():
  ex_river_routing(1,None)

def test_river_routing_1_1():
  ex_river_routing(1,1)

def test_backward_xy():
  ex_backward_xy()

def test_write_globalrouting_json_symmetric():
  ex_write_globalrouting_json( ex_symmetric(1,1))

def test_write_globalrouting_json_symmetric():
  ex_write_globalrouting_json( ex_river_routing(1,None))

def test_ota():
  aux_from_json( 'ota')

def test_ota_bigger():
  aux_from_json( 'ota_bigger')

def test_sc():
  aux_from_json( 'sc')


import argparse

if __name__ == "__main__":
  parser = argparse.ArgumentParser( description="Global router placer for collection of designs")

  parser.add_argument( "-n", "--block_name", type=str, required=True)

  args = parser.parse_args()

  if args.block_name == "ota_symmetric":
    ex_write_globalrouting_json( ex_symmetric(1,1))
  else:
    aux_from_json( args.block_name)
