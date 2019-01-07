# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 22:19:39 2018

@author: kunal
"""
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import isomorphism
import numpy as np

def merge_nodes(G,Htype,argv,matched_ports):
    G_copy=G.copy()
    for node in argv:
        if not G.nodes[node]:
            print("node not in graph anymore")
            return G, nx.multigraph
    #print("Is input bipartite",nx.is_bipartite(G))
    assert len(argv) > 1
   #  print("Merging nodes",argv)
    new_node=""
    ports={}
    subgraph = nx.MultiGraph()
    for node in argv:
        new_node +='_'+node
        subgraph.add_node(node, inst_type=G.nodes[node]["inst_type"],
                          ports=G.nodes[node]['ports'],
                          edge_weight=G.nodes[node]['edge_weight'],
                          values=G.nodes[node]['values']
                          )
        #print(G.nodes[node])
        nbr=G.neighbors(node)
        for ele in nbr:
            if ele not in subgraph.nodes():
                subgraph.add_node(ele, inst_type=G.nodes[ele]["inst_type"],
                                  net_type=G.nodes[ele]["net_type"])
                         
            subgraph.add_edge(node, ele, weight=G[node][ele][0]["weight"])
            #print("adding edge b/w:",node,ele,G[node][ele][0]["weight"])
            
            if ele in ports:
                ports[ele] += G[node][ele][0]["weight"]
            else:
                ports[ele] = G[node][ele][0]["weight"]
        
        
        #G.add_edge(new_node,ele,weight=wt)
    new_node=new_node[1:]
    G.add_node(new_node,inst_type=Htype,ports_match=matched_ports)
    
    for pins in list(ports):
        if set (G.neighbors(pins)) <= set(argv):
            del ports[pins]
            #print("deleting node",pins)
            G.remove_node(pins)
    for node in argv:
        G.remove_node(node)
    for pins in ports:
        G.add_edge(new_node,pins,weight=ports[pins])
        #print("new ports",pins,ports[pins])


    #nx.write_yaml(subgraph,"subgraph.yaml")
    #nx.write_yaml(G_copy,"graph.yaml")

    #print("Is output bipartite",nx.is_bipartite(G))
    #print("Is subgraph bipartite",nx.is_bipartite(G))
#    for node in G_copy:
#        print(G_copy[node])
#    for node in subgraph:
#        print(node,"subg node",subgraph.nodes[node])
#        print(node,"main node",G_copy.nodes[node])

    GM = isomorphism.GraphMatcher(G_copy,subgraph,node_match=isomorphism.categorical_node_match(['inst_type'],['metal',1]))
#    GM = isomorphism.GraphMatcher(G_copy,subgraph)
    
    if  not GM.subgraph_is_isomorphic():
        #print("isomorphism check fail")
        print("")


    return G, subgraph
