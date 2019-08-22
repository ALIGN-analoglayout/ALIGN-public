from satplacer.global_router import Tech, Grid, ex_write_globalrouting_json

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


