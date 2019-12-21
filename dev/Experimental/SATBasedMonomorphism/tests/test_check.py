import networkx as nx

from sgi import *

def test_check_monomorphism_succeeds():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2)])

    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(1,2)])

    pi = [1,0,2]

    assert check_monomorphism( g, h, pi)

def test_check_monomorphism_fails():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2)])

    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(1,2)])

    pi = [0,1,2]

    assert not check_monomorphism( g, h, pi)

def test_check_subgraph_isomorphism_succeeds():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2)])

    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(1,0), (1,2)])

    pi = [1,0,2]

    assert check_subgraph_isomorphism( g, h, pi)

def test_check_subgraph_isomorphism_fails():
    g = nx.Graph()
    g.add_nodes_from( [0, 1, 2])
    g.add_edges_from( [(0,1), (0,2)])

    h = nx.Graph()
    h.add_nodes_from( [0, 1, 2])
    h.add_edges_from( [(1,0),(1,2)])

    pi = [0,1,2]

    assert not check_subgraph_isomorphism( g, h, pi)
