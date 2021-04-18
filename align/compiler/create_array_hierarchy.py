# -*- coding: utf-8 -*-
"""
Created on Wed July 08 13:12:15 2020

@author: kunal
"""

from collections import Counter
from itertools import combinations
from .merge_nodes import merge_nodes
from .util import compare_two_nodes
from ..schema import constraint

import logging
logger = logging.getLogger(__name__)

def matching_groups(G,level1,ports_weight):
    """
    Creates a a 2D list from 1D list of level1, grouping similar elements in separate group

    Parameters
    ----------
    G : TYPE
        DESCRIPTION.
    level1 : TYPE
        DESCRIPTION.
    ports_weight : TYPE
        DESCRIPTION.
    Returns
    -------
    similar_groups : TYPE
        DESCRIPTION.

    """
    
    similar_groups=[]
    logger.debug(f"creating groups for all neighbors: {level1}")
    #modify this best case complexity from n*(n-1) to n complexity
    for l1_node1,l1_node2 in combinations(level1, 2):
        if compare_two_nodes(G,l1_node1,l1_node2,ports_weight):
            found_flag=0
            logger.debug("similar_group %s",similar_groups)
            for index, sublist in enumerate(similar_groups):
                if l1_node1 in sublist and l1_node2 in sublist:
                    found_flag=1
                    break
                if l1_node1 in sublist:
                    similar_groups[index].append(l1_node2)
                    found_flag=1
                    break
                elif l1_node2 in sublist:
                    similar_groups[index].append(l1_node1)
                    found_flag=1
                    break
            if found_flag==0:
                similar_groups.append([l1_node1,l1_node2])
    return similar_groups



def trace_template(graph, similar_node_groups,visited,template,array):
    next_match={}
    traversed=visited.copy()

    for source,groups in similar_node_groups.items():
        next_match[source]=[]
        for node in groups:
            level1=list(set(graph.neighbors(node))- set(traversed))
            next_match[source] +=level1
            visited +=level1
        if len(next_match[source])==0:
            del next_match[source]

    if len(next_match.keys())> 0 and match_branches(graph,next_match) :
        for source in array.keys():
            if source in next_match.keys():
                array[source]+=next_match[source]
         
        template +=next_match[list(next_match.keys())[0]]
        logger.debug("found matching level: %s,%s,%s",template,similar_node_groups,visited)
        if check_convergence(next_match):
            trace_template(graph, next_match,visited,template,array)

def match_branches(graph,nodes_dict):
    logger.debug(f"matching next level branches {nodes_dict}")
    nbr_values = {}
    for node, nbrs in nodes_dict.items():
        #super_dict={}
        super_list=[]
        if len(nbrs)==1:
            return False
        for nbr in nbrs:
            if graph.nodes[nbr]['inst_type']== 'net':
                super_list.append('net')
                super_list.append(graph.nodes[nbr]['net_type'])
            else:
                super_list.append(graph.nodes[nbr]['inst_type'])
                for v in graph.nodes[nbr]['values'].values():
                    super_list.append(v)
        nbr_values[node]=Counter(super_list)
    _,main=nbr_values.popitem()
    for node, val in nbr_values.items():
        if val == main:
            continue
        else:
            return False
    return True


def check_convergence(match:dict):
    vals=[]
    for val in match.values():
        if set(val).intersection(vals):
            return False
        else:
            vals+=val


def create_hierarchy(graph,node:str,traversed:list,ports_weight:dict):
    """
    Creates array hierarchies starting from input node

    Parameters
    ----------
    graph : TYPE
        DESCRIPTION.
    node : str
        DESCRIPTION.
    traversed : list
        DESCRIPTION.
    ports_weight : dict
        DESCRIPTION.

    Returns
    -------
    hier_of_node : TYPE
        DESCRIPTION.

    """

    hier_of_node ={}
    level1 = list(set(graph.neighbors(node))-set(traversed))
    
    hier_of_node[node]=matching_groups(graph,level1,None)
    logger.debug(f"new hierarchy points {hier_of_node} from node {node}")

    if len(hier_of_node[node]) > 0:
        for group in sorted(hier_of_node[node] , key=lambda group: len(group)):
            if len(group)>0:
                templates = {}
                similar_node_groups = {}
                for el in sorted(group):
                    similar_node_groups[el]=[el]
                templates[node] = [el]
                visited = group
                array = similar_node_groups.copy()
                trace_template(graph,similar_node_groups,visited,templates[node],array)
                logger.debug(f"similar groups final from {node}:{array}")
        
        #check number of levels in detected array
        #single hierarchy arrays can be handled using simple approaches
        all_inst = []
        if array and len(array.values())>1 and len(list(array.values())[0])>1:
            #Multiple hierarchy identified in array
            matched_ports = {}
            for branch in  array.values():
                for node_hier in branch:
                    if graph.nodes[node_hier]['inst_type'] != 'net' \
                        and node_hier not in all_inst \
                        and not graph.nodes[node_hier]['inst_type'].lower().startswith('cap'):  
                        all_inst.append(node_hier)
                
        else:
            hier_of_node[node]=[]
            for inst in array.keys():
                if graph.nodes[inst]['inst_type']!='net':
                    hier_of_node[node].append(inst)
        if len(all_inst)>1:
            all_inst=sorted(all_inst)
            h_ports_weight={}
            for inst in  all_inst:
                for node_hier in list(set(graph.neighbors(inst))):
                    if graph.nodes[node_hier]['inst_type']== 'net':
                        if (set(graph.neighbors(node_hier))- set(all_inst)) or graph.nodes[node_hier]["net_type"]=='external':
                            matched_ports[node_hier] = node_hier
                            h_ports_weight[node_hier] = []
                            for nbr in list(graph.neighbors(node_hier)):
                                h_ports_weight[node_hier].append(graph.get_edge_data(node_hier, nbr)['weight'])
                       
            logger.debug(f"creating a new hierarchy for {node}, {all_inst}, {matched_ports}")
            subgraph,_ = merge_nodes(
                    graph, 'array_hier_'+node,all_inst , matched_ports)
            hier_of_node[node]={
                        "name": 'array_hier_'+node,
                        "graph": subgraph,
                        "ports": list(matched_ports.keys()),
                        "ports_match": matched_ports,
                        "ports_weight": h_ports_weight,
                        "constraints": constraint.ConstraintDB(),
                        "size": len(subgraph.nodes())
                    }
        return hier_of_node
