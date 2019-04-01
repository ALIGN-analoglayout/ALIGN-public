import networkx as nx
import networkx.algorithms.isomorphism

from sgi import *

def test_monomorphic_but_not_isomorphic():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2), (1,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1), (0,2)])

    m = networkx.algorithms.isomorphism.GraphMatcher( g, h)
    assert not m.subgraph_is_isomorphic()

def test_ssm():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1),(0,2),(1,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2)])

    assert sat_subgraph_monomorphism(g,h)

def test_ssi():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1),(0,2),(1,2)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2)])

    assert not sat_subgraph_isomorphism(g,h)

def test_ssm2():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2, 3])
    g.add_edges_from( [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2),(1,2)])

    assert sat_subgraph_monomorphism(g,h)

def test_ssi2():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2, 3])
    g.add_edges_from( [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)])
    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(0,1),(0,2),(1,2)])

    assert sat_subgraph_isomorphism(g,h)

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

def test_pickled_files_ssm():
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

def test_pickled_files_ssi():
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

    assert sat_subgraph_isomorphism(gg,hh)
