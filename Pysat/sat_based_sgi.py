import tally
import networkx as nx
import networkx.algorithms.isomorphism

def test_monomorphic_but_not_isomorphic():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2), (1,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1), (0,2)])

    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert not m.subgraph_is_isomorphic()

def sat_subgraph_monomorphism( g, h):
    # h is a subgraph g
    # each vertex in h maps to some vertex in g
    # set up two dimensional array

    s = tally.Tally()
    mgr = tally.VarMgr( s)

    lst = []
    for n in g.nodes:
        lst.append( mgr.add_var( tally.BitVec( s, str(n), len(h.nodes))))
        s.emit_at_most_one( lst[-1].vars)

    for (idx,n) in enumerate(h.nodes):
        l = []
        for bv in lst:
            l.append( bv.vars[idx])
        s.emit_exactly_one( l)

    for eh in h.edges:
        # if eh in h.edges, then map(eh) must be in g.edges
        lits = []
        for eg in g.edges:
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[0]].vars[eh[0]], lst[eg[1]].vars[eh[1]]], lits[-1])
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[1]].vars[eh[0]], lst[eg[0]].vars[eh[1]]], lits[-1])
        s.add_clause( lits)

    s.solve()

    if s.state == 'SAT':
        for bv in lst:
            print( bv.val())

    if False:
        res_tbl = []

        for (idx,n) in enumerate(h.nodes):
            res = None
            for (jdx,bv) in enumerate(lst):
                if bv.val[idx]:
                    res = jdx
            assert res is not None
            res_tbl.append( res)

        print( res_tbl)


    return s.state == 'SAT'

def test_ssm():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1),(0,2),(1,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2)])

    assert sat_subgraph_monomorphism(g,h)

def gen_mirror_bank( nmirrors):
    h = nx.Graph()

    node_count = 1 + 2 * (1 + nmirrors)
    
    h.add_nodes_from( list(range(node_count)))

    device_offset = 1 + 1 + nmirrors
    # ref
    h.add_edges_from( [(0,device_offset), (1,device_offset)])

    # mirrors
    for i in range(nmirrors):
        h.add_edges_from( [(0,device_offset+1+i),(1,device_offset+1+i),(2+i,device_offset+1+i)])
        
    return h

def gen_mirror_bank2( nmirrors):
    h = nx.Graph()

    node_count = 1 + 4 * (1 + nmirrors)
    
    h.add_nodes_from( list(range(node_count)))

    device_offset = 1 + 2 * (1 + nmirrors)
    # ref
    h.add_edges_from( [(0,device_offset), (1,device_offset),   (2,device_offset),
                                          (1,device_offset+1), (2,device_offset+1)])

    # mirrors
    for i in range(nmirrors):
        h.add_edges_from( [(0,device_offset+2*(1+i)),
                           (2,device_offset+2*(1+i)),
                           (3+2*i,device_offset+2*(1+i)),
                           (3+2*i,device_offset+2*(1+i)+1),
                           (4+2*i,device_offset+2*(1+i)+1)])
        
    return h

def test_ssm_mirrors():
    g = gen_mirror_bank( 20)
    h = gen_mirror_bank( 19)
    assert sat_subgraph_monomorphism(g,h)

def test_networkx_sgi_mirrors():
    g = gen_mirror_bank( 20)
    h = gen_mirror_bank( 19)
    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert m.subgraph_is_isomorphic()

def test_ssm_mirrors2():
    g = gen_mirror_bank2( 20)
    h = gen_mirror_bank2( 19)
    assert sat_subgraph_monomorphism(g,h)

def test_networkx_sgi_mirrors2():
    g = gen_mirror_bank2( 20)
    h = gen_mirror_bank2( 19)
    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert m.subgraph_is_isomorphic()

def test_pickled_files():
    g = nx.read_gpickle( "__G1")
    h = nx.read_gpickle( "__G2")

    def abstract_graph( g):
        tbl = {}
        for (idx,n) in enumerate(g.nodes):
            tbl[n] = idx

        gg = nx.Graph()
        gg.add_nodes_from( range(len(g.nodes)))

        es = set( (tbl[e[0]],tbl[e[1]]) for e in g.edges)
        gg.add_edges_from( list(es))
        return gg

    gg = abstract_graph( g)
    hh = abstract_graph( h)

    print( len(g.nodes), len(g.edges), len(gg.edges))
    print( len(h.nodes), len(h.edges), len(hh.edges))


    assert sat_subgraph_monomorphism(gg,hh)

def xxx_test_pickled_files_nx():
    g = nx.read_gpickle( "__G1")
    h = nx.read_gpickle( "__G2")

    def abstract_graph( g):
        tbl = {}
        for (idx,n) in enumerate(g.nodes):
            tbl[n] = idx

        gg = nx.Graph()
        gg.add_nodes_from( range(len(g.nodes)))

        es = set( (tbl[e[0]],tbl[e[1]]) for e in g.edges)
        gg.add_edges_from( list(es))
        return gg

    gg = abstract_graph( g)
    hh = abstract_graph( h)

    print( len(g.nodes), len(g.edges), len(gg.edges))


    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert m.subgraph_is_isomorphic()
