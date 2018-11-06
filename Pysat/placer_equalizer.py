from placer import *

def test_vga_bigger():

    nmirror = CellLeaf( "nmirror", Rect(0,0,8,4))
    nmirror.addTerminal( "d1", Rect(0,0,0,4))
    nmirror.addTerminal( "g1", Rect(2,0,2,4))
    nmirror.addTerminal( "s", Rect(4,0,4,4))
    nmirror.addTerminal( "g2", Rect(6,0,6,4))
    nmirror.addTerminal( "d2", Rect(8,0,8,4))

    ndiffpair = CellLeaf( "ndiffpair", Rect(0,0,8,4))
    ndiffpair.addTerminal( "d1", Rect(0,0,0,4))
    ndiffpair.addTerminal( "g1", Rect(2,0,2,4))
    ndiffpair.addTerminal( "s", Rect(4,0,4,4))
    ndiffpair.addTerminal( "g2", Rect(6,0,6,4))
    ndiffpair.addTerminal( "d2", Rect(8,0,8,4))

    res = CellLeaf( "res", Rect(0,0,8,4))
    res.addTerminal( "t1", Rect(0,0,0,4))
    res.addTerminal( "t2", Rect(8,0,8,4))

    groundedcap = CellLeaf( "groundedcap", Rect(0,0,8,4))
    groundedcap.addTerminal( "t", Rect(0,0,0,4))

    vga = CellHier( "vga")

    vga.addInstance( CellInstance( "MCM00_MCM01", nmirror))
    vga.addInstance( CellInstance( "MDP01_MDP00", ndiffpair))
    vga.addInstance( CellInstance( "R1", res))
    vga.addInstance( CellInstance( "R0", res))
    vga.addInstance( CellInstance( "Cload1", groundedcap))
    vga.addInstance( CellInstance( "Cload2", groundedcap))

    vga.connect('MCM00_MCM01', 'd1', 'vmirror')
    vga.connect('MCM00_MCM01', 'g1', 'vmirror')
    vga.connect('MCM00_MCM01', 's', 'gnd!')
    vga.connect('MCM00_MCM01', 'g2', 'vmirror')
    vga.connect('MCM00_MCM01', 'd2', 'net3')

    vga.connect('MDP01_MDP00', 'd1', 'vout1')
    vga.connect('MDP01_MDP00', 'g1', 'vin2')
    vga.connect('MDP01_MDP00', 's', 'net3')
    vga.connect('MDP01_MDP00', 'g2', 'vin1')
    vga.connect('MDP01_MDP00', 'd2', 'vout2')

    vga.connect('R1', 't1', 'vdd!')
    vga.connect('R1', 't2', 'vout1')

    vga.connect('R0', 't1', 'vdd!')
    vga.connect('R0', 't2', 'vout2')

    vga.connect('Cload1', 't', 'vout1')
    vga.connect('Cload2', 't', 'vout2')

    nx = 12
    ny = 30

    vga.bbox = Rect( 0, 0, nx, ny)

    s = tally.Tally()
    r = Raster( s, vga, nx, ny)
    r.semantic()

    #put a raft on the left and right
    for x in [0,nx-1]:
      for y in range(ny):
        for ri in r.ris:
          print( ri.ci.nm, x, y)
          s.emit_never( ri.filled.var( r.idx( x, y)))

    for x in range(nx):
      for y in range(ny):
        for ri in r.ris:
          if y % 4 != 0:
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

    with open( "mydesign_dr_globalrouting.json", "wt") as fp:
        tech = Tech()
        vga.write_globalrouting_json( fp, tech)

    with open( "vga_bigger_placer_out.json", "wt") as fp:
        tech = Tech()
        vga.dumpJson( fp, tech)

if __name__ == "__main__":
    test_vga_bigger()
