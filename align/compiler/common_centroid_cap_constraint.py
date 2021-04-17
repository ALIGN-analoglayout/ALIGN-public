#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Feb 29 12:02:52 2020

@author: kunal001
"""
import os
from math import ceil

from .merge_nodes import merge_nodes
from .write_constraint import symmnet_device_pairs	
import logging
import json
logger = logging.getLogger(__name__)

def CapConst(graph,name,unit_size_cap,input_const,merge_caps):
    """
    Reads input graph and generates constraints for capacitors
    The constraints are defined such that caps are designed using a unit cap.
    Parameters
    ----------
    graph : networkx graph
        Input graph to be modified
    input_dir: pathlib.path
        Input const directory path to check available constraints
    name : string
        Sub circuit name. Constraints are generated for sub circuits seperately
    Returns
    -------
    None.

    """

    available_cap_const = []
    if input_const and 'constraints' in input_const:
        all_const = input_const["constraints"]
        for const in input_const["constraints"]:
            if const["const_name"] == 'GroupCaps':
                available_cap_const.append(const["cap_name"])
    else:
        input_const = {}
        all_const = []

    logger.debug(f"Searching cap constraints for block {name}, input const: {all_const}")
    if merge_caps:
        cc_cap_size = merge_symmetric_caps(all_const, graph, unit_size_cap, available_cap_const)
    else:
        cc_cap_size={}	
    logger.debug(f"Writing constraints for remaining caps in the circuit graph {name}")
    for node, attr in graph.nodes(data=True):
        if attr['inst_type'].lower().startswith('cap_')  and node not in available_cap_const:
            logger.debug(f"writing cap constraint for node {node} {cc_cap_size}")
            if 'cap' in attr['values'].keys():
                size = attr['values']["cap"]*1E15
            else:
                size = unit_size_cap
            if node in cc_cap_size:
                n_cap=cc_cap_size[node]
            else:
                n_cap = ceil(size/unit_size_cap)
            if not isinstance(n_cap,list) and n_cap > 128:
                unit_block_name = 'Cap_' + str(int(round(size,1))) + 'f'
                n_cap = 1
            else:
                unit_block_name = 'Cap_' + str(unit_size_cap) + 'f'
            cap_const = {"const_name": "GroupCaps",
                        "blocks": [node],
                        "name": node,
                        "num_units": n_cap,
                        "unit_cap": unit_block_name,
                        "dummy": True
                        }

            logger.debug(f"Cap constraint {cap_const}")
            all_const.append(cap_const)
            available_cap_const.append(node)
    input_const["constraints"] = all_const
    logger.debug(f"Identified cap constraints of {name} are {input_const}")

    return input_const

def merge_symmetric_caps(all_const, graph, unit_size_cap, available_cap_const):
    """
    Converts symmetry constraints between caps as common-centroid constraint.
    It merges the caps and returns merged size for writing constraints
    Args:
        all_const ([dict]): all constraints of a hierarchy
        graph ([nx.graph]): sub-circuit graph
        unit_size_cap ([string]): name of unit size cap
        available_cap_const ([dict]): existing constraints

    Returns:
        [dict]: name:size of caps for which constraints are modified from symmetry to common cetroid
    """
    cap_array={}
    for const in all_const:
        if const["const_name"]== "SymmetricBlocks":
            b = [p for p in const["pairs"] if len(p) == 2]
            for pair in const["pairs"]:
                if len(pair) == 2:
                    inst = pair[0]
                    if inst in graph and graph.nodes[inst]['inst_type'].lower().startswith('cap') \
                        and len (graph.nodes[inst]['ports'])==2: #Not merge user provided const
                        logger.debug("merging cap cc constraints:%s",b)
                        p1, p2 = sorted(pair, key=lambda c: graph.nodes[c]['values']["cap"] * 1E15)
                        cap_array[p1]={p1:[p1,p2]}
                        pair[0]= "_".join([p1,p2])
                        pair.pop()

    logger.debug(f"Updating circuit graph by merging caps: {cap_array}")
    cc_cap_size={}	
    for array in cap_array.values():
        n_cap=[]
        cc_caps=[]
        for arr in array.values():
            for ele in arr:
                if ele in graph.nodes() and graph.nodes[ele]['inst_type'].lower().startswith('cap') and \
                    ele not in available_cap_const:
                    if 'cap' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["cap"]*1E15
                    else:
                        size = unit_size_cap
                    n_cap.append( ceil(size/unit_size_cap))
                    cc_caps.append(ele)
            if cc_caps:
                cc_cap = '_'.join(cc_caps)
                logger.debug(f"merging symmetrical caps: {arr} {cc_cap} {cc_caps} {n_cap}")
                ctype = 'Cap_cc_'+"_".join([str(x) for x in n_cap])
                merge_caps(graph, ctype, cc_caps, cc_cap)
                cc_cap_size[cc_cap] = n_cap
    # updating any symmnet constraint 	
    for id, const in enumerate(all_const):
        if const["const_name"] == "SymmetricNets":
            print(const)
            net1 = const['net1']	
            net2 = const['net2']
            existing = ""
            logger.debug(f"updating symmnet constraint {const}")
            removed_blocks1 = [pin.split('/')[0]  for pin in const['pins1'] if net1 in graph.nodes() \
                and pin.split('/')[0] not in graph.nodes()]	
            removed_blocks2 = [pin.split('/')[0]  for pin in const['pins2'] if net2 in graph.nodes() \
                and pin.split('/')[0] not in graph.nodes()]	
            removed_blocks = removed_blocks1 + removed_blocks2
            if removed_blocks:	
                pairs, s1, s2 = symmnet_device_pairs(graph, net1, net2, existing)	
                if pairs:	
                    symmNetj = {"const_name": "SymmetricNets", "direction": "V", "net1": net1, "net2": net2, "pins1": s1, "pins2": s2}
                    all_const[id] =symmNetj	
                else:	
                    logger.debug("skipped symmnet on net1 {net1} and net2 {}")
    return cc_cap_size

def merge_caps(graph, name, caps, inst):
    """
    Merges caps in graph as single cap
    Parameters
    ----------
    graph : networkx graph
        Input graph to be modified
    caps : list
        Used to check nets which should not be deleted/renamed.
    Returns
    -------
    None.

    """

    matched_ports ={}
    for idx,cap in enumerate(caps):
        #cc_pair.update({cap_block: updated_cap})
        conn = list(graph.neighbors(cap))
        matched_ports['MINUS'+str(idx)] = conn[0]
        matched_ports['PLUS'+str(idx)]= conn[1]
    #line = line.replace(caps_in_line,updated_cap)
    merge_nodes(graph, name ,caps , matched_ports, inst)
