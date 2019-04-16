# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 22:19:39 2018

@author: kunal
"""
import networkx as nx
from networkx.algorithms import isomorphism


def merge_nodes(G, hier_type, argv, matched_ports):
    """ Merges the  given nodes in argv and returns a
     reduced graph. It also returns a subgraph(not used anymore)"""

    g_copy = G.copy()
    for node in argv:
        if not G.nodes[node]:
            print("node not in graph anymore")
            return G, nx.Graph
    #print("Is input bipartite",nx.is_bipartite(G))
    assert len(argv) > 1
    #  print("Merging nodes",argv)
    new_node = ""
    ports = {}
    subgraph = nx.Graph()
    all_values = []
    for node in argv:
        new_node += '_' + node
        subgraph.add_node(node,
                          inst_type=G.nodes[node]["inst_type"],
                          ports=G.nodes[node]['ports'],
                          edge_weight=G.nodes[node]['edge_weight'],
                          values=G.nodes[node]['values'])
        all_values.extend(G.nodes[node]['values'])
        #print(G.nodes[node])
        nbr = G.neighbors(node)
        for ele in nbr:
            if ele not in subgraph.nodes():
                subgraph.add_node(ele,
                                  inst_type=G.nodes[ele]["inst_type"],
                                  net_type=G.nodes[ele]["net_type"])

            #print("adding edge b/w:",node,ele,G[node][ele]["weight"])
            subgraph.add_edge(node, ele, weight=G[node][ele]["weight"])

            if ele in ports:
                ports[ele] += G[node][ele]["weight"]
            else:
                ports[ele] = G[node][ele]["weight"]

        #G.add_edge(new_node,ele,weight=wt)
    new_node = new_node[1:]
    G.add_node(new_node,
               inst_type=hier_type,
               ports_match=matched_ports,
               values=all_values)

    for pins in list(ports):
        if set(G.neighbors(pins)) <= set(argv):
            del ports[pins]
            #print("deleting node",pins)
            G.remove_node(pins)
    for node in argv:
        G.remove_node(node)
    for pins in ports:
        G.add_edge(new_node, pins, weight=ports[pins])
        #print("new ports",pins,ports[pins])

    #nx.write_yaml(subgraph,"subgraph.yaml")
    #nx.write_yaml(g_copy,"graph.yaml")

    #print("Is output bipartite",nx.is_bipartite(G))
    #print("Is subgraph bipartite",nx.is_bipartite(G))


#    for node in g_copy:
#        print(g_copy[node])
#    for node in subgraph:
#        print(node,"subg node",subgraph.nodes[node])
#        print(node,"main node",g_copy.nodes[node])

    graph_match = isomorphism.GraphMatcher(
        g_copy,
        subgraph,
        node_match=isomorphism.categorical_node_match(['inst_type'],
                                                      ['metal', 1]))
    #    GM = isomorphism.GraphMatcher(g_copy,subgraph)

    if not graph_match.subgraph_is_isomorphic():
        print("isomorphism check fail")

    return G, subgraph
