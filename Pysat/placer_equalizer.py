from placer import *

def test_mirrors():

    ux = 4
    uy = 1

    nunit = CellLeaf( "nunit", Rect(0,0,ux,uy))
    nunit.addTerminal( "s1", Rect(0,0,0,uy))
    nunit.addTerminal( "g1", Rect(1,0,1,uy))
    nunit.addTerminal( "d", Rect(2,0,2,uy))
    nunit.addTerminal( "g2", Rect(3,0,3,uy))
    nunit.addTerminal( "s2", Rect(4,0,4,uy))

    mirrors = CellHier( "mirrors")

    configs = [('4',8,'out4'),('2',4,'out2'),('1a',2,'out1a'),('1b',2,'out1b'),('ref',2,'vmirror')]

    for (tag, mult, _) in configs:
        for i in range(mult):
            mirrors.addInstance( CellInstance( "CM_%s_%d" % (tag,i), nunit))

    for (tag, mult, d) in configs:
        for i in range(mult):
            mirrors.connect( "CM_%s_%d" % (tag,i), 's1', 'gnd!')
            mirrors.connect( "CM_%s_%d" % (tag,i), 'g1', 'vmirror')
            mirrors.connect( "CM_%s_%d" % (tag,i), 'd',  d)
            mirrors.connect( "CM_%s_%d" % (tag,i), 'g2', 'vmirror')
            mirrors.connect( "CM_%s_%d" % (tag,i), 's2', 'gnd!')

    nnx = 6
    nny = 3

    nx = nnx*ux
    ny = nny*uy

    mirrors.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, mirrors, nx, ny)
    r.semantic()

#
# Assign common centroid placement
#
    places = [('4',0,2),('4',1,2), ('4',2,2),  ('4',3,2),  ('1b',4,2),('2',5,2),
              ('2',0,1),('1a',1,1),('ref',2,1),('ref',3,1),('1a',4,1),('2',5,1)]
    # should generalize the '1' at some point
    places_common_centroid = [ (tag,nnx-1-x,nny-1-y) for (tag,x,y) in places if y != 1]

    od = OrderedDict()
    for (tag,x,y) in places + places_common_centroid:
        if tag not in od: od[tag] = []
        od[tag].append( (tag,x,y))

    ri_tbl = { ri.ci.nm: ri for ri in r.ris}
    for (tag,v) in od.items():
        for (idx,(tag,x,y)) in enumerate(v):
            s.emit_always( ri_tbl["CM_%s_%i" % (tag,idx)].anchor.var( r.idx( x*ux, y*uy)))


    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0:
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    s.solve()
    assert s.state == 'SAT'

    specified_nets = set()
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [ list(tup) for tup in chunk( remaining_nets, 6)]

    r.optimizeNets( groups)

    mirrors.dump()
    with open("__json","wt") as fp:
        r.dump_for_animation( fp)


def test_diffpairs1x():

    ux = 4
    uy = 1

    nunit = CellLeaf( "nunit", Rect(0,0,ux,uy))
    nunit.addTerminal( "s1", Rect(0,0,0,uy))
    nunit.addTerminal( "g1", Rect(1,0,1,uy))
    nunit.addTerminal( "d", Rect(2,0,2,uy))
    nunit.addTerminal( "g2", Rect(3,0,3,uy))
    nunit.addTerminal( "s2", Rect(4,0,4,uy))

    dp = CellHier( "dp1x")

    configs = [('a',2,'outa','ina','so'),('b',2,'outb','inb','so'),('s',2,'si','c','so')]

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.addInstance( CellInstance( "DP_%s_%d" % (tag,i), nunit))

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.connect( "DP_%s_%d" % (tag,i), 's1', s)
            dp.connect( "DP_%s_%d" % (tag,i), 'g1', g)
            dp.connect( "DP_%s_%d" % (tag,i), 'd',  d)
            dp.connect( "DP_%s_%d" % (tag,i), 'g2', g)
            dp.connect( "DP_%s_%d" % (tag,i), 's2', s)

    nnx = 6
    nny = 1

    nx = nnx*ux
    ny = nny*uy

    dp.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, dp, nx, ny)
    r.semantic()

#
# Assign common centroid placement
#
    places = [('s',0,0),('a',1,0),('b',2,0)]
    # generalize the '0' below
    places_common_centroid = [ (tag,nnx-1-x,0) for (tag,x,y) in places]

    od = OrderedDict()
    for (tag,x,y) in places + places_common_centroid:
        if tag not in od: od[tag] = []
        od[tag].append( (tag,x,y))

    ri_tbl = { ri.ci.nm: ri for ri in r.ris}
    for (tag,v) in od.items():
        for (idx,(tag,x,y)) in enumerate(v):
            s.emit_always( ri_tbl["DP_%s_%i" % (tag,idx)].anchor.var( r.idx( x*ux, y*uy)))


    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0:
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    s.solve()
    assert s.state == 'SAT'

    specified_nets = set()
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [ list(tup) for tup in chunk( remaining_nets, 6)]

    r.optimizeNets( groups)

    dp.dump()
    with open("__json","wt") as fp:
        r.dump_for_animation( fp)



def test_diffpairs2x():

    ux = 4
    uy = 1

    nunit = CellLeaf( "nunit", Rect(0,0,ux,uy))
    nunit.addTerminal( "s1", Rect(0,0,0,uy))
    nunit.addTerminal( "g1", Rect(1,0,1,uy))
    nunit.addTerminal( "d", Rect(2,0,2,uy))
    nunit.addTerminal( "g2", Rect(3,0,3,uy))
    nunit.addTerminal( "s2", Rect(4,0,4,uy))

    dp = CellHier( "dp2x")

    configs = [('a',4,'outa','ina','so'),('b',4,'outb','inb','so'),('s',4,'si','c','so')]

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.addInstance( CellInstance( "DP_%s_%d" % (tag,i), nunit))

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.connect( "DP_%s_%d" % (tag,i), 's1', s)
            dp.connect( "DP_%s_%d" % (tag,i), 'g1', g)
            dp.connect( "DP_%s_%d" % (tag,i), 'd',  d)
            dp.connect( "DP_%s_%d" % (tag,i), 'g2', g)
            dp.connect( "DP_%s_%d" % (tag,i), 's2', s)

    nnx = 6
    nny = 2

    nx = nnx*ux
    ny = nny*uy

    dp.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, dp, nx, ny)
    r.semantic()

#
# Assign common centroid placement
#
    ri_tbl = { ri.ci.nm: ri for ri in r.ris}        

    if True:
      places = [('s',0,1),('a',1,1),('a',2,1),('b',3,1),('b',4,1),('s',5,1)]
      places_common_centroid = [ (tag,nnx-1-x,nny-1-y) for (tag,x,y) in places]

      od = OrderedDict()
      for (tag,x,y) in places + places_common_centroid:
        if tag not in od: od[tag] = []
        od[tag].append( (tag,x,y))

      for (tag,v) in od.items():
        for (idx,(tag,x,y)) in enumerate(v):
            s.emit_always( ri_tbl["DP_%s_%i" % (tag,idx)].anchor.var( r.idx( x*ux, y*uy)))

    if True:
      assert nx % ux == 0
      assert ny % uy == 0

      nny = ny//uy
      assert nny % 2 == 0
      cy = (nny // 2)*uy

      def xys():
        for y in range(ny-uy,-uy,-uy):
          for x in range(0,nx,ux):
            yield (x,y)

      # lexigraphic order
      for (tag, mult, _, _, _) in configs:
        print( tag, mult)
        assert mult % 2 == 0
        for i in range(0,mult//2):
          for j in range(i+1,mult//2):
            nm = "DP_%s_%d" % (tag,i)
            nm_other = "DP_%s_%d" % (tag,j)
            ri = ri_tbl[nm]
            ri_other = ri_tbl[nm_other]

            for (ai,(ax,ay)) in enumerate( xys()):
              for (bi,(bx,by)) in enumerate( xys()):
                if bi <= ai:
                  print( ai,(ax,ay), bi,(bx,by), nm, nm_other)
                  s.emit_implies( ri.anchor.var( r.idx( ax, ay)),
                                  -ri_other.anchor.var( r.idx( bx, by)))

      for (tag, mult, _, _, _) in configs:
        assert mult % 2 == 0
        for i in range(mult//2):
          nm = "DP_%s_%d" % (tag,i)
          nm_other = "DP_%s_%d" % (tag,mult//2+i)

          ri = ri_tbl[nm]
          ri_other = ri_tbl[nm_other]

          # disallow drivers below common centroid
          for x in range(0,nx,ux):
            for y in range(0,cy,uy):
              s.emit_never( ri.anchor.var( r.idx( x,y)))

          # Enforce common centroid
          for x in range(nx):
            if x % ux != 0: continue
            for y in range(ny):
              if y % uy != 0: continue
              x_other = (nx//ux-1-x//ux)*ux
              y_other = (ny//uy-1-y//uy)*uy
              s.emit_implies( ri.anchor.var( r.idx( x,y)),
                              ri_other.anchor.var( r.idx( x_other, y_other)))
            
    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0 or x % ux != 0: 
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
#            s.emit_never( ri.anchorMY.var( r.idx( x,y))) # these cells are symmetrically in x
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    print( "First solve start")
    s.solve()
    assert s.state == 'SAT'
    print( "First solve end")

    if False:
      # enumerate all solutions
      def clauseEliminatingCurrentSolution():
        clause = []
        for x in range(0,nx,ux):
          for y in range(0,ny,uy):
            idx = r.idx( x, y)
            for ri in r.ris:
              val = ri.anchor.val( idx)
              var = ri.anchor.var( idx)
              if val is True:
                clause.append( -var)  
              elif val is False:
                clause.append(  var)  
        return clause

      assumptions = []
      r.record()
      while s.state == 'SAT':
        c = clauseEliminatingCurrentSolution()  
        assumptions.append( c)
        s.add_clause( c)
        print( "Solve start", len(assumptions))
        s.solve()
        if s.state == 'SAT':
          r.record()
          print( "Solve end", len(assumptions))
        else:
          print( "Solve end (failed)", len(assumptions))

      with open("__json","wt") as fp:
        r.dump_for_animation( fp)

    out_nets = ["outb","outa"]
    in_nets  = ["ina","inb"]
    s_nets  = ["si","so"]
    ctrl_nets = ["c"]

    specified_nets = set(out_nets + in_nets + s_nets + ctrl_nets)
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [out_nets,in_nets,s_nets,ctrl_nets] + [ list(tup) for tup in chunk( remaining_nets, 6)]

    print("Groups:", groups)

    r.optimizeNets( groups)

    dp.dump()
    with open("__json","wt") as fp:
        r.dump_for_animation( fp)

def test_diffpairs4x():

    ux = 4
    uy = 1

    nunit = CellLeaf( "nunit", Rect(0,0,ux,uy))
    nunit.addTerminal( "s1", Rect(0,0,0,uy))
    nunit.addTerminal( "g1", Rect(1,0,1,uy))
    nunit.addTerminal( "d", Rect(2,0,2,uy))
    nunit.addTerminal( "g2", Rect(3,0,3,uy))
    nunit.addTerminal( "s2", Rect(4,0,4,uy))

    dp = CellHier( "dp4x")

    configs = [('a',8,'outa','ina','so'),('b',8,'outb','inb','so'),('s',8,'si','c','so')]

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.addInstance( CellInstance( "DP_%s_%d" % (tag,i), nunit))

    for (tag, mult, d, g, s) in configs:
        for i in range(mult):
            dp.connect( "DP_%s_%d" % (tag,i), 's1', s)
            dp.connect( "DP_%s_%d" % (tag,i), 'g1', g)
            dp.connect( "DP_%s_%d" % (tag,i), 'd',  d)
            dp.connect( "DP_%s_%d" % (tag,i), 'g2', g)
            dp.connect( "DP_%s_%d" % (tag,i), 's2', s)

    nnx = 6
    nny = 4

    nx = nnx*ux
    ny = nny*uy

    dp.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, dp, nx, ny)
    r.semantic()

#
# Assign common centroid placement
#
    places = [('s',0,3),('a',1,3),('a',2,3),('b',3,3),('b',4,3),('s',5,3),
              ('s',0,2),('a',1,2),('a',2,2),('b',3,2),('b',4,2),('s',5,2)]
    places_common_centroid = [ (tag,nnx-1-x,nny-1-y) for (tag,x,y) in places]

    od = OrderedDict()
    for (tag,x,y) in places + places_common_centroid:
        if tag not in od: od[tag] = []
        od[tag].append( (tag,x,y))

    ri_tbl = { ri.ci.nm: ri for ri in r.ris}
    for (tag,v) in od.items():
        for (idx,(tag,x,y)) in enumerate(v):
            s.emit_always( ri_tbl["DP_%s_%i" % (tag,idx)].anchor.var( r.idx( x*ux, y*uy)))


    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0:
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    s.solve()
    assert s.state == 'SAT'

    specified_nets = set()
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [ list(tup) for tup in chunk( remaining_nets, 6)]

    r.optimizeNets( groups)

    dp.dump()
    with open("__json","wt") as fp:
        r.dump_for_animation( fp)


def test_ca(optimize=True):
    ux = 1
    uy = 1

    pitch = 0.072 # um
    cap = 0.1 # fF/um

    pitches_per_ux = 4
    pitches_per_uy = 4
    layers = 3

    cap_per_ux_uy = cap*pitch*pitches_per_ux*pitches_per_uy*layers

    cap_per_unit = 8*8*cap_per_ux_uy

    print( "cap_per_ux_uy: %f cap_per_unit %f" % (cap_per_ux_uy, cap_per_unit))

    cunit = CellLeaf( "cunit", Rect(0,0,8*ux,8*uy))
    for x in [0,8]:
        for (tag,l,u) in [("t0",1,3),("t1",5,7)]:
            cunit.addTerminal( tag, Rect(x*ux,l*uy,x*ux,u*uy))

    ca = CellHier( "ca")

    configs = [('c', 8, 't0','t1')]

    for (tag, mult, t0, t1) in configs:
        for i in range(mult):
            ca.addInstance( CellInstance( "CA_%s_%d" % (tag,i), cunit))

    for (tag, mult, t0, t1) in configs:
        for i in range(mult):
            ca.connect( "CA_%s_%d" % (tag,i), 't0', t0)
            ca.connect( "CA_%s_%d" % (tag,i), 't1', t1)

    nx = 2*8*ux
    ny = 4*8*uy

    ca.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, ca, nx, ny)
    r.semantic()


#
# Assign common centroid placement
#
    places = [('s',0,3),('a',1,3),('a',2,3),('b',3,3),('b',4,3),('s',5,3),
              ('s',0,2),('a',1,2),('a',2,2),('b',3,2),('b',4,2),('s',5,2)]
    places_common_centroid = [ (tag,5-x,3-y) for (tag,x,y) in places]

    od = OrderedDict()
    for (tag,x,y) in places + places_common_centroid:
        if tag not in od: od[tag] = []
        od[tag].append( (tag,x,y))

    ri_tbl = { ri.ci.nm: ri for ri in r.ris}
    for (tag,v) in od.items():
        for (idx,(tag,x,y)) in enumerate(v):
            pass
#            s.emit_always( ri_tbl["CA_%s_%i" % (tag,idx)].anchor.var( r.idx( 1+x*ux, y*uy)))


    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0:
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    s.solve()
    assert s.state == 'SAT'

    specified_nets = set()
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [ list(tup) for tup in chunk( remaining_nets, 6)]

    r.optimizeNets( groups)

    ca.dump()

def test_vga(optimize=True):
    ux = 4
    uy = 8


    mirrors = CellLeaf( "mirrors", Rect(0,0,6*ux,4*uy))
    mirrors.addTerminal( "out4", Rect(0,0,0,uy))
    mirrors.addTerminal( "out2", Rect(1,0,1,uy))
    mirrors.addTerminal( "out1a", Rect(2,0,2,uy))
    mirrors.addTerminal( "out1b", Rect(3,0,3,uy))
    mirrors.addTerminal( "vmirror", Rect(4,0,4,uy))

    dp1 = CellLeaf( "dp1", Rect(0,0,4*ux,2*uy))
    dp1.addTerminal( "outa", Rect(0,0,0,uy))
    dp1.addTerminal( "outb", Rect(1,0,1,uy))
    dp1.addTerminal( "ina", Rect(2,0,2,uy))
    dp1.addTerminal( "inb", Rect(3,0,3,uy))
    dp1.addTerminal( "si", Rect(4,0,4,uy))
    dp1.addTerminal( "c", Rect(5,0,5,uy))

    dp2 = CellLeaf( "dp2", Rect(0,0,4*ux,4*uy))
    dp2.addTerminal( "outa", Rect(0,0,0,uy))
    dp2.addTerminal( "outb", Rect(1,0,1,uy))
    dp2.addTerminal( "ina", Rect(2,0,2,uy))
    dp2.addTerminal( "inb", Rect(3,0,3,uy))
    dp2.addTerminal( "si", Rect(4,0,4,uy))
    dp2.addTerminal( "c", Rect(5,0,5,uy))

    dp4 = CellLeaf( "dp4", Rect(0,0,6*ux,4*uy))
    dp4.addTerminal( "outa", Rect(0,0,0,uy))
    dp4.addTerminal( "outb", Rect(1,0,1,uy))
    dp4.addTerminal( "ina", Rect(2,0,2,uy))
    dp4.addTerminal( "inb", Rect(3,0,3,uy))
    dp4.addTerminal( "si", Rect(4,0,4,uy))
    dp4.addTerminal( "c", Rect(5,0,5,uy))

    vga = CellHier( "vga")

    io = [("outa","outa"),("outb","outb"),("ina","ina"),("inb","inb")]

    vga.addAndConnect( mirrors, "m", [("out4","v4"),("out2","v2"),("out1a","v1a"),("out1b","v1b"),("vmirror","vmirror")])
    vga.addAndConnect( dp1, "dp1a", io + [("si","v1a"),("c","c1a")])
    vga.addAndConnect( dp1, "dp1b", io + [("si","v1b"),("c","c1b")])
    vga.addAndConnect( dp2, "dp2",  io + [("si","v2"),("c","c2")])
    vga.addAndConnect( dp4, "dp4",  io + [("si","v4"),("c","c4")])

    nx = 6*ux
    ny = 16*uy
#    nx = (2*5)*ux
#    ny = 8*uy
#    nx = 2+(2*4+2*6)*ux+6
#    ny = 4*uy

    vga.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, vga, nx, ny)
    r.semantic()

    places = [
        ('dp1b',0,14),
        ('dp1a',0,12),
        ('dp2',0,8),
        ('m',0,4),
        ('dp4',0,0)
    ]

    od = OrderedDict()
    for (tag,x,y) in places:
        assert tag not in od
        od[tag] = (x,y)

    ri_tbl = { ri.ci.nm: ri for ri in r.ris}
    for (tag,(x,y)) in od.items():
        pass
#        s.emit_always( ri_tbl[tag].anchor.var( r.idx( x*ux, y*uy)))

    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % uy != 0:
            s.emit_never( ri.anchor.var( r.idx( x,y)))
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMY.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))
          else:
            s.emit_never( ri.anchorMX.var( r.idx( x,y)))
            s.emit_never( ri.anchorMXY.var( r.idx( x,y)))

    s.solve()
    assert s.state == 'SAT'

    drv_nets = ["v1a","v1b","v2", "v4"]
    out_nets = ["outa","outb"]
    in_nets  = ["ina","inb"]
    ctrl_nets = ["c1a","c1b","c2", "c4"]

    specified_nets = set(out_nets + in_nets + drv_nets + ctrl_nets)
    remaining_nets = [ n for n in r.nets.keys() if n not in specified_nets]

    def chunk( it, size):
      it = iter(it)
      return iter( lambda: tuple(itertools.islice(it, size)), ())

    groups = [drv_nets,out_nets,in_nets,ctrl_nets] + [ list(tup) for tup in chunk( remaining_nets, 6)]

    print("Groups:", groups)

    if optimize:
        r.optimizeNets( groups)
    else:
        r.solve()

    vga.dump()
    with open("__json","wt") as fp:
        r.dump_for_animation( fp)


import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description="Placer equalizer")
    parser.add_argument( "-n", "--block_name", type=str, required=True)
    parser.add_argument( "-noopt", "--no_optimize", action='store_true')

    args = parser.parse_args()

    if args.block_name == "vga":
        test_vga( not args.no_optimize)
    elif args.block_name == "ca":
        test_ca( not args.no_optimize)
    elif args.block_name == "mirrors":
        test_mirrors()
    elif args.block_name == "diffpairs1x":
        test_diffpairs1x()
    elif args.block_name == "diffpairs2x":
        test_diffpairs2x()
    elif args.block_name == "diffpairs4x":
        test_diffpairs4x()
    else:
        assert(False)

