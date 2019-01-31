import tally
import networkx as nx
import networkx.algorithms.isomorphism

def test_monomorphic_but_not_isomorphic():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1), (0,2), (1,2)])

    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert not m.subgraph_is_isomorphic()

def sat_subgraph_monomorphism( g, h):
    # g is a subgraph h
    # each vertex in g maps to some vertex in h
    # set up two dimensional array

    s = tally.Tally()
    mgr = tally.VarMgr( s)

    gtbl = {}
    for (idx,n) in enumerate(g.nodes):
        gtbl[n] = idx

    htbl = {}
    for (idx,n) in enumerate(h.nodes):
        htbl[n] = idx

    lst = []
    for n in h.nodes:
        lst.append( mgr.add_var( tally.BitVec( s, str(n), len(g.nodes))))
        s.emit_exactly_one( lst[-1].vars)

    for (idx,n) in enumerate(g.nodes):
        l = []
        for bv in lst:
            l.append( bv.vars[idx])
        s.emit_at_most_one( l)

    for eg in g.edges:
        # if eg in g.edges, then map(eg) must be in h.edges
        ug = gtbl[eg[0]]
        vg = gtbl[eg[1]]

        lits = []
        for eh in h.edges:
            uh = htbl[eh[0]]
            vh = htbl[eh[1]]

            lits.append( s.add_var())
            s.emit_and( [ lst[uh].vars[ug], lst[vh].vars[vg]], lits[-1])
            lits.append( s.add_var())
            s.emit_and( [ lst[vh].vars[ug], lst[uh].vars[vg]], lits[-1])
            
        s.add_clause( lits)

    s.solve()

    if s.state == 'SAT':
        for bv in lst:
            print( bv.val())

    return s.state == 'SAT'

def test_ssm():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1),(0,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2),(1,2)])

    assert sat_subgraph_monomorphism(g,h)


if __name__ == "__main__":
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1),(0,2),(1,2)])
    h = nx.Graph()
    h.add_nodes_from( ['a', 'b', 'c'])
    h.add_edges_from( [('a','b'), ('a','c')])

    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    print( m.subgraph_is_isomorphic())

    #
    # Can't currently check monomorphisms:
    #    So this is false
    #
