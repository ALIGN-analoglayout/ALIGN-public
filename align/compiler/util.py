# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
import os
from re import sub
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import bipartite
from ..schema.graph import Graph
import logging
logger = logging.getLogger(__name__)

def get_next_level(subckt,G, tree_l1):
    """get_next_level traverse graph and get next connected element
    Does not traverse Connections through Gate or Body of transistors identified as 'B','G' pins
    TODO: check this skip hierarchically

    [extended_summary]

    Args:
        subckt ([type]): [description]
        G ([type]): [description]
        tree_l1 ([type]): [description]

    Returns:
        [type]: [description]
    """
    tree_next=[]
    for node in list(tree_l1):
        assert subckt.get_element(node) or node in subckt.nets, f"{node} not present in {subckt.elements} {subckt.nets}"
        if subckt.get_element(node) and get_base_model(subckt,node) and 'MOS' in get_base_model(subckt,node):
            for nbr in list(G.neighbors(node)):
                if set(G.get_edge_data(node, nbr)['pin']) - set({'G','B'}):
                    tree_next.append(nbr)
        elif node in subckt.nets:
            for nbr in list(G.neighbors(node)):
                base_model = get_base_model(subckt,nbr)
                if base_model and 'MOS' in base_model and \
                set(G.get_edge_data(node, nbr)['pin']) - set({'G','B'}):
                    tree_next.append(nbr)
                else:
                    tree_next.append(nbr)
        else:
            tree_next.extend(list(G.neighbors(node)))
    return tree_next

def get_base_model(subckt,node):
    assert subckt.get_element(node)
    if subckt.get_element(node).model in ['NMOS','PMOS','RES','CAP']:
        base_model = subckt.get_element(node).model
    elif subckt.parent.find(subckt.get_element(node).model):
        base_model = subckt.parent.find(subckt.get_element(node).model).base
    else:
        logger.warning(f"invalid device {node}")
    return base_model
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
    nbrs1= [nbr for nbr in G.neighbors(node1) if G.get_edge_data(node1, nbr)['pin']!= {'G'}]
    nbrs2= [nbr for nbr in G.neighbors(node2) if G.get_edge_data(node2, nbr)['pin']!= {'G'}]
    nbrs1= [nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['pin'] !={'B'}]
    nbrs2= [nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)['pin'] !={'B'}]
    logger.debug(f"comparing_nodes: {node1},{node2},{nbrs1},{nbrs2}")

    # Add some heuristic here in future
    if G.nodes[node1].get('instance'):
        logger.debug(f"checking match between {node1} {node2}")
        in1 = G.nodes[node1].get('instance')
        in2 = G.nodes[node2].get('instance')
        if in1.model == in2.model and\
            len(set(in1.pins.values())) == len(set(in2.pins.values()))  and \
            in1.parameters == in2.parameters:
            logger.debug(" True")
            return True
        else:
            logger.debug(" False, value mismatch")
            return False
    else:
        nbrs1_type= sorted([G.nodes[nbr].get('instance').model for nbr in nbrs1])
        nbrs2_type= sorted([G.nodes[nbr].get('instance').model for nbr in nbrs2])
        if nbrs1_type != nbrs2_type:
            logger.debug(f"type mismatch {nbrs1}:{nbrs1_type} {nbrs2}:{sorted(nbrs2_type)}")
            return False
        if node1 in ports_weight and node2 in ports_weight:
            if sorted(ports_weight[node1]) == sorted(ports_weight[node2]):
                logger.debug("True")
                return True
            else:
                logger.debug(f'external port weight mismatch {ports_weight[node1]},{ports_weight[node2]}')
                return False
        else:
            weight1=[G.get_edge_data(node1, nbr)['pin'] for nbr in nbrs1]
            weight2=[G.get_edge_data(node2, nbr)['pin'] for nbr in nbrs2]
            if {'G'} in weight1:
                weight1.remove({'G'})
            if {'G'} in weight2:
                weight2.remove({'G'})
            if weight2==weight1:
                logger.debug("True")
                return True
            else:
                logger.debug(f'internal port weight mismatch {weight1},{weight2}')
                return False

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
    nx.write_yaml(Graph(graph), dir_path+'/' + filename + ".yaml")

def convert_to_unit(values):
    for param in values:
        if float(values[param])>= 1 :
            values[param]=int(values[param])
        elif float(values[param])*1E3> 1 :
            values[param]=str(int(values[param]*1E3))+'m'
        elif float(values[param])*1E6>1 :
            values[param]=str(int(values[param]*1E6))+'u'
        elif float(values[param])*1E9>1:
            values[param]=str(int(values[param]*1E9))+'n'
        elif float(values[param])*1E12>1:
            values[param]=str(int(values[param]*1E12))+'p'
        elif float(values[param])*1E15>1:
            values[param]=str(int(values[param]*1E15))+'f'
        else:
            logger.error(f"WRONG value, {values}")
