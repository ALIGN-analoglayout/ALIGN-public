#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Feb 29 12:02:52 2020

@author: kunal001
"""
from align.schema.types import set_context
import os
from math import ceil

from .merge_nodes import merge_nodes
from .find_constraint import symmnet_device_pairs
import logging
import json
from ..schema import constraint
from ..schema.graph import Graph

logger = logging.getLogger(__name__)

def CapConst(ckt_data,name,unit_size_cap,merge_caps):
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
    subckt = ckt_data.find(name)
    graph = Graph(subckt)
    all_const = subckt.constraints
    available_cap_const = []
    for const in all_const:
        if isinstance(const, constraint.GroupCaps):
            available_cap_const.append(const.name)
    if available_cap_const:
        logger.debug(f"Available cap constraints, input const: {available_cap_const}")
    # if merge_caps:
    #     cc_cap_size = merge_symmetric_caps(all_const, graph, unit_size_cap, available_cap_const)
    # else:
    cc_cap_size={}
    logger.debug(f"Writing constraints for remaining caps in the circuit graph {name}")
    for ele in subckt.elements:
        if ele.model == 'CAP'  and ele.name not in available_cap_const:
            logger.debug(f"writing cap constraint for node {ele} {cc_cap_size}")
            if 'VALUE' in ele.parameters.keys():
                size = float(ele.parameters["VALUE"])*1E15
            else:
                size = unit_size_cap
            if ele.name in cc_cap_size:
                n_cap = cc_cap_size[ele.name]
            else:
                n_cap = [ceil(size/unit_size_cap)]
            if not isinstance(n_cap,list) and n_cap > 128:
                unit_block_name = 'Cap_' + str(int(round(size,1))) + 'f'
                n_cap = [1]
            else:
                unit_block_name = 'Cap_' + str(unit_size_cap) + 'f'
            with set_context(subckt.constraints):
                cap_const = constraint.GroupCaps(
                            instances = [ele.name],
                            name = ele.name,
                            num_units = n_cap,
                            unit_cap = unit_block_name,
                            dummy = False
                            )
                logger.debug(f"Cap constraint {cap_const}")
                all_const.append(cap_const)
            available_cap_const.append(ele.name)
    logger.debug(f"Identified cap constraints of {name} are {all_const}")

    return all_const

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
        if isinstance(const, constraint.SymmetricBlocks):
            b = [p for p in const.pairs if len(p) == 2]
            for pair in const.pairs:
                if len(pair) == 2:
                    inst = pair[0]
                    if inst in graph and graph.nodes[inst].get('instance').model=='CAP' \
                        and len (graph.nodes[inst].get('instance').pins)==2: #Not merge user provided const
                        logger.debug("Symmetric cap constraints:%s",b)
                        p1, p2 = sorted(pair, key=lambda c: float(graph.nodes[c].get('instance').parameters["VALUE"]) * 1E15)
                        cap_array[p1]={p1:[p1,p2]}
                        pair[0]= "_".join([p1,p2])
                        pair.pop()

    logger.debug(f"Updating symmetric cap pairs by merging caps: {cap_array} not in {available_cap_const}")
    cc_cap_size = {}
    for array in cap_array.values():
        n_cap=[]
        cc_caps=[]
        for arr in array.values():
            for ele in arr:
                if ele in graph.nodes() and graph.nodes[ele].get('instance').model=='CAP' and \
                    ele not in available_cap_const:
                    if 'VALUE' in graph.nodes[ele].get('instance').parameters.keys():
                        size = float(graph.nodes[ele].get('instance').parameters["VALUE"])*1E15
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
    for index, const in enumerate(all_const):
        if isinstance(const, constraint.SymmetricNets):
            net1 = const.net1.upper()
            net2 = const.net2.upper()
            logger.debug(f"updating symmnet constraint {const}")
            if const.pins1:
                removed_blocks1 = [pin.split('/')[0]  for pin in const.pins1 if net1 in graph.nodes() \
                    and pin.split('/')[0] not in graph.nodes()]
                removed_blocks2 = [pin.split('/')[0]  for pin in const.pins2 if net2 in graph.nodes() \
                    and pin.split('/')[0] not in graph.nodes()]
                removed_blocks = removed_blocks1 + removed_blocks2
            pairs, s1, s2 = symmnet_device_pairs(graph, net1, net2)
            print(s1,s2)
            if pairs:
                symmNetj = constraint.SymmetricNets(
                    direction = "V",
                    net1 = net1,
                    net2 = net2,
                    pins1 = s1,
                    pins2 = s2)
                all_const[index] =symmNetj
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
    logger.info(f"creating common-centorid cap {caps}")
    matched_ports ={}
    for idx,cap in enumerate(caps):
        #cc_pair.update({cap_block: updated_cap})
        conn = list(graph.neighbors(cap))
        matched_ports['MINUS'+str(idx)] = conn[0]
        matched_ports['PLUS'+str(idx)]= conn[1]
    #line = line.replace(caps_in_line,updated_cap)
    merge_nodes(graph, name ,caps , matched_ports, inst)
