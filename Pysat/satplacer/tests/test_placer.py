from tally import tally
from satplacer.placer import Tech, Raster, CellLeaf, Rect, CellHier, CellInstance

def test_build_raster():
    s = tally.Tally()
    raster = Raster( s, 'xy', 4, 10)

    s.solve()
    assert s.state == 'SAT'

def test_flat_hier():

    l = CellLeaf( "ndev")
    l.addTerminal( "sd0", Rect(0,0,0,1))
    l.addTerminal( "sd1", Rect(1,0,1,1))

    h = CellHier( "flat")

    nx = 20
    ny = 10

    for x in range(nx):
      for y in range(ny):
        inst_name = 'u_%d_%d' % (x,y)
        h.addInstance( CellInstance( inst_name, l))
        h.instances[inst_name].fa_map['sd0'] = 'a_%d_%d' % (x+1,y)
        h.instances[inst_name].fa_map['sd1'] = 'a_%d_%d' % (x+0,y)

    s = tally.Tally()
    r = Raster( s, h, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}
    for x in range(nx):
      for y in range(ny):
        inst_name = 'u_%d_%d' % (x,y)
        for xx in range(nx):
          for yy in range(ny):
#            s.emit_never( ri_map[inst_name].anchor.var(    r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMY.var(  r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMX.var(  r.idx( xx, yy)))
            s.emit_never( ri_map[inst_name].anchorMXY.var( r.idx( xx, yy)))

    for y in range(ny):
      for x in range(nx):
        inst_name = 'u_%d_%d' % (x,y)
        s.emit_always( ri_map[inst_name].anchor.var( r.idx( nx-1-x, y)))

    r.solve()
    h.updateBbox()
        
    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        h.write_globalrouting_json( fp, tech)

def test_grid_hier():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b1 = CellLeaf( "block1", Rect(0,0,2,4))

    m = 4

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    for i in range(m):
      inst_name = 'v%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b1)

    nx = 9
    ny = 9

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()
    r.solve()
    g.updateBbox()

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)

def test_hier():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b0.addTerminal( "l0", Rect(0,0,0,1))
    b0.addTerminal( "l1", Rect(0,1,0,2))
    b0.addTerminal( "r0", Rect(4,0,4,1))
    b0.addTerminal( "r1", Rect(4,1,4,2))

    m = 2

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    g.instances['u0'].fa_map['l0'] = 'a'
    g.instances['u0'].fa_map['l1'] = 'b'
    g.instances['u0'].fa_map['r0'] = 'c'
    g.instances['u0'].fa_map['r1'] = 'd'

    g.instances['u1'].fa_map['l0'] = 'a'
    g.instances['u1'].fa_map['l1'] = 'b'
    g.instances['u1'].fa_map['r0'] = 'd'
    g.instances['u1'].fa_map['r1'] = 'c'

    nx = 8
    ny = 2

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}

    #place in corner
    s.emit_always( ri_map['u0'].anchor.var( r.idx( 0, 0)))

    r.solve()
    g.updateBbox()

    assert ri_map['u1'].anchorMXY.val( r.idx(nx-1,ny-1)) is True

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)

def test_non_unit_pins():

    b0 = CellLeaf( "block0", Rect(0,0,4,2))
    b0.addTerminal( "l", Rect(0,0,0,2))
    b0.addTerminal( "r", Rect(4,0,4,2))

    m = 2

    g = CellHier( "grid")
    for i in range(m):
      inst_name = 'u%d' % i
      g.instances[inst_name] = CellInstance( inst_name, b0)

    g.instances['u0'].fa_map['l'] = 'a'
    g.instances['u0'].fa_map['r'] = 'b'

    g.instances['u1'].fa_map['l'] = 'b'
    g.instances['u1'].fa_map['r'] = 'c'

    nx = 8
    ny = 2

    s = tally.Tally()
    r = Raster( s, g, nx, ny)
    r.semantic()

    ri_map = { ri.ci.nm : ri for ri in r.ris}

    #place in corner
    s.emit_always( ri_map['u0'].anchor.var( r.idx( 0, 0)))

    for x in range(nx):
      for y in range(ny):
        pass
        s.emit_never( ri_map['u1'].anchor.var( r.idx( x, y)))
#        s.emit_never( ri_map['u1'].anchorMX.var( r.idx( x, y)))
        s.emit_never( ri_map['u1'].anchorMY.var( r.idx( x, y)))
        s.emit_never( ri_map['u1'].anchorMXY.var( r.idx( x, y)))

    r.solve()
    g.updateBbox()

    assert ri_map['u1'].anchorMX.val( r.idx(4,1)) is True

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        g.write_globalrouting_json( fp, tech)






