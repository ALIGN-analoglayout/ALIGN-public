#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Feb 29 12:02:52 2020

@author: kunal001
"""
import os
from math import ceil

from .merge_nodes import merge_nodes

import logging
import json
logger = logging.getLogger(__name__)



def WriteCap(graph,input_dir,name,unit_size_cap,all_array):
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
    const_path = input_dir / (name + '.const.json')
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for input constraints {const_path}')
        with open(const_path, "r") as const_fp:
            all_const=json.load(const_fp)
    else:
        return
    logger.debug(f"Existing common centroid caps: {all_array}")

    #Change covert symmBlock const between caps to common centroid caps
    available_cap_const = []
    for const in all_const["constraints"]:
        if const["const_name"]== "SymmBlock":
            b = [[p["block1"],p["block2"]] for p in const["pairs"] if p["type"]=="sympair"]

            for pair in const["pairs"]:
                if pair["type"]=="sympair":
                    inst=pair["block1"]
                    if inst in graph and graph.nodes[inst]['inst_type'].lower().startswith('cap'):
                        logger.debug("merging cap cc constraints:%s",b)
                        p1,p2=sorted([pair["block1"],pair["block2"]], key=lambda c:graph.nodes[c]['values']["cap"]*1E15)
                        all_array[p1]={p1:[p1,p2]}
                        pair["type"]="selfsym"
                        pair["block"]= "_".join([p1,p2])
                        del pair["block1"]
                        del pair["block2"]
    with open(const_path, 'w') as outfile:
        json.dump(all_const, outfile, indent=4)

    logger.debug(f"Updating circuit graph by merging caps: {all_array}")
    cc_cap_size={}
    for array in all_array.values():
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
                merge_caps(graph,cc_caps)
                cc_cap_size[cc_cap]=n_cap

    logger.debug("Writing constraints for remaining caps in the circuit graph")
    for node, attr in graph.nodes(data=True):
        if attr['inst_type'].lower().startswith('cap')  and node not in available_cap_const:
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
                n_cap=1
            else:
                unit_block_name = 'Cap_' + str(unit_size_cap) + 'f'
            cap_const = { "const_name":"CC",
                        "cap_name": node,
                        "size":n_cap,
                        "unit_capacitor": unit_block_name,
                        "nodummy": True,
                        "cap_r":-1,
                        "cap_s":-1
                        }

            logger.debug(f"Cap constraint {cap_const}")
            all_const["constraints"].append(cap_const)
            available_cap_const.append(node)

    if len(all_const["constraints"]) ==0:
        os.remove(const_path)
        logger.debug("no cap const found: %s",const_path)
    else:
        with open(const_path, 'w') as outfile:
            json.dump(all_const, outfile, indent=4)
        logger.debug("added cap const: %s",const_path)

def check_common_centroid(graph,const_path,ports):
    """
    Reads common centroid const in generated constraints
    Merges cc caps as single cap in const-file and netlist
    Parameters
    ----------
    graph : networkx graph
        Input graph to be modified
    const_path: pathlib.path
        Input const file path
    ports : list
        Used to check nets which should not be deleted/renamed.
    Returns
    -------
    None.

    """
    #new_const_path = const_path.parents[0] / (const_path.stem + '.const_temp')
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for common centroid {const_path}')
        with open(const_path, "r") as const_fp:
            all_const=json.load(const_fp)
    else:
        return

    for const in all_const["constraints"]:
        logger.debug(f"{const}")
        if  const["const_name"]== "CC" \
            and isinstance(const["cap_name"],list):
            logger.debug("Fixing cc constraint for caps:%s",const)
            caps = const["cap_name"]
            cc_cap = "_".join(caps)
            const["cap_name"] = cc_cap
            merge_caps(graph,caps)

    with open(const_path, 'w') as outfile:
        json.dump(all_const, outfile, indent=4)

def merge_caps(graph, caps):
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
    graph, _,_= merge_nodes(
            graph, 'Cap_cc',caps , matched_ports)
