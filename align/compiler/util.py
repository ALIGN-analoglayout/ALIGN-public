# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
import os
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import bipartite

import logging
logger = logging.getLogger(__name__)

def get_next_level(G, tree_l1):
    tree_next=[]
    for node in list(tree_l1):
        if node not in G.nodes:
            continue
        # logger.debug(f"neighbors of {node}: {list(G.neighbors(node))}")
        if 'mos' in G.nodes[node]["inst_type"]:
            for nbr in list(G.neighbors(node)):
                if G.get_edge_data(node, nbr)['weight']!=2:
                    tree_next.append(nbr)
        elif 'net' in G.nodes[node]["inst_type"]:
            for nbr in list(G.neighbors(node)):
                if 'mos' in G.nodes[nbr]["inst_type"] and \
                G.get_edge_data(node, nbr)['weight']!=2:
                    tree_next.append(nbr)
                elif 'mos' not in G.nodes[nbr]["inst_type"]:
                    tree_next.append(nbr)               
        else:
            tree_next.extend(list(G.neighbors(node)))
    # logger.debug(f"next nodes {tree_next} ")
    return tree_next
def compare_two_nodes(G,node1:str,node2:str ,ports_weight):
    """
    compare two node properties. It uses 1st level of neighbourhood for comparison of nets

    Parameters
    ----------
    G : TYPE, networkx graph
        DESCRIPTION. it consist of all subckt properties
    node1, node2 : TYPE  string
        DESCRIPTION. node name
    ports_weight : TYPE list
        DESCRIPTION. port weights 

    Returns
    -------
    bool
        DESCRIPTION. True for matching node

    """
    nbrs1= [nbr for nbr in G.neighbors(node1) if G.get_edge_data(node1, nbr)['weight'] !=2]
    nbrs2= [nbr for nbr in G.neighbors(node2) if G.get_edge_data(node2, nbr)['weight'] !=2]
    nbrs1= [nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['weight'] !=7]
    nbrs2= [nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)['weight'] !=7]
    logger.debug(f"comparing_nodes: {node1},{node2},{nbrs1},{nbrs2}")

    # Add some heuristic here in future
    
    nbrs1_type= sorted([G.nodes[nbr]["inst_type"] for nbr in nbrs1]) + [G.nodes[node1]["inst_type"]]
    nbrs2_type= sorted([G.nodes[nbr]["inst_type"] for nbr in nbrs2]) + [G.nodes[node2]["inst_type"]]
    if nbrs1_type != nbrs2_type:
        logger.debug(f"type mismatch {nbrs1}:{nbrs1_type} {nbrs2}:{sorted(nbrs2_type)}")
        return False
    if G.nodes[node1]["inst_type"]=="net": 
        if G.nodes[node1]["net_type"] == G.nodes[node2]["net_type"] == 'external':
            if not ports_weight:
                return True
            elif sorted(ports_weight[node1]) == sorted(ports_weight[node2]):
                logger.debug("True")
                return True
            else:
                logger.debug(f'external port weight mismatch {ports_weight[node1]},{ports_weight[node2]}')
                return False
        elif G.nodes[node1]["net_type"] == 'internal':
            weight1=[(G.get_edge_data(node1, nbr)['weight'] & ~2) for nbr in nbrs1]
            weight2=[(G.get_edge_data(node2, nbr)['weight'] & ~2) for nbr in nbrs2]
            if weight2==weight1:
                logger.debug("True")
                return True
            else:
                logger.debug(f'internal port weight mismatch {weight1},{weight2}')
                return False
    else: 
        if 'values' in G.nodes[node1].keys() and \
        G.nodes[node1]["values"]==G.nodes[node2]["values"]:
            logger.debug(" True")
            return True
        else:
            logger.debug(" False, value mismatch")
            return False  
  
def max_connectivity(G):
    conn_value =0
    #internal_nets =[x for x,y in G.nodes(data=True) if y['inst_type']=='net' and len(G.edges(x)) > 1]
    #Drain and source weights are equal
    for (u, v, wt) in G.edges.data('weight'):
        if G.nodes[u]['inst_type']=='net' and len(G.edges(u)) >1 and wt<8:
            if 'mos' in G.nodes[v]['inst_type'] and wt >3:
                conn_value-=3
            conn_value +=wt
            #print (u,conn_value)
        elif G.nodes[v]['inst_type']=='net' and len(G.edges(v)) >1 and wt<8:
            if 'mos' in G.nodes[u]['inst_type'] and wt >3:
                conn_value-=3
            conn_value +=wt
            #print (v,conn_value)
    return conn_value
def plt_graph(subgraph,sub_block_name):
    copy_graph=subgraph
    for node,attr in list(copy_graph.nodes(data=True)):
        if 'source' in attr["inst_type"]:
            copy_graph.remove_node(node)

    no_of_transistor =len([x for x,y in subgraph.nodes(data=True) if 'net' not in y['inst_type']] )
    Title=sub_block_name+", no of devices:"+ str(no_of_transistor)
    if no_of_transistor > 10 :
        plt.figure(figsize=(8, 6))
    else:
        plt.figure(figsize=(4, 3))
    nx.draw(copy_graph,with_labels=True,pos=nx.spring_layout(copy_graph))
    plt.title(Title, fontsize=20)

def _show_circuit_graph(filename, graph, dir_path):
    #print(graph)
    no_of_subgraph = 0
    for subgraph in nx.connected_component_subgraphs(graph):
        no_of_subgraph += 1

        color_map = []

        plt.figure(figsize=(6, 8))
        for _, attr in subgraph.nodes(data=True):
            if "inst_type" in attr:
                if attr["inst_type"] == 'pmos':
                    color_map.append('red')
                elif attr["inst_type"] == 'nmos':
                    color_map.append('cyan')
                elif attr["inst_type"] == 'cap':
                    color_map.append('orange')
                elif attr["inst_type"] == 'net':
                    color_map.append('pink')
                else:
                    color_map.append('green')
        nx.draw(subgraph, node_color=color_map)
        plt.title(filename, fontsize=20)
        if not os.path.exists(dir_path):
            os.mkdir(dir_path)
        plt.savefig(dir_path+'/'+ filename + "_" +
                    str(no_of_subgraph) + '.png')
        plt.close()

def _show_bipartite_circuit_graph(filename, graph, dir_path):
    no_of_subgraph = 0
    for subgraph in nx.connected_component_subgraphs(graph):
        no_of_subgraph += 1

        color_map = []
        x_pos, y_pos = bipartite.sets(subgraph)
        pos = dict()
        pos.update(
            (n, (1, i)) for i, n in enumerate(x_pos))  # put nodes from X at x=1
        pos.update(
            (n, (2, i)) for i, n in enumerate(y_pos))  # put nodes from Y at x=2
        #nx.draw(B, pos=pos)
        #plt.show()
        plt.figure(figsize=(6, 8))
        for dummy, attr in subgraph.nodes(data=True):
            if "inst_type" in attr:
                if attr["inst_type"] == 'pmos':
                    color_map.append('red')
                elif attr["inst_type"] == 'nmos':
                    color_map.append('cyan')
                elif attr["inst_type"] == 'cap':
                    color_map.append('orange')
                elif attr["inst_type"] == 'net':
                    color_map.append('pink')
                else:
                    color_map.append('green')
        nx.draw(subgraph, node_color=color_map, with_labels=True, pos=pos)
        plt.title(filename, fontsize=20)
        if not os.path.exists(dir_path):
            os.mkdir(dir_path)
        plt.savefig(dir_path+'/' + filename + "_" +
                    str(no_of_subgraph) + '.png')
        plt.close()

def _write_circuit_graph(filename, graph,dir_path):
    if not os.path.exists(dir_path):
        os.mkdir(dir_path)
    nx.write_yaml(graph, dir_path+'/' + filename + ".yaml")

def convert_to_unit(values):
    for param in values:
        if values[param]>= 1 :
            values[param]=int(values[param])
        elif values[param]*1E3> 1 :
            values[param]=str(int(values[param]*1E3))+'m'
        elif values[param]*1E6>1 :
            values[param]=str(int(values[param]*1E6))+'u'
        elif values[param]*1E9>1:
            values[param]=str(int(values[param]*1E9))+'n'
        elif values[param]*1E12>1:
            values[param]=str(int(values[param]*1E12))+'p'
        elif values[param]*1E15>1:
            values[param]=str(int(values[param]*1E15))+'f'
        else:
            logger.error(f"WRONG value, {values}")
