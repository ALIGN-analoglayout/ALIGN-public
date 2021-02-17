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

def WriteCap(graph,name,unit_size_cap,input_const):
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
    # const_path = input_dir / (name + '.const.json')
    # if os.path.isfile(const_path):
    #     logger.debug(f'Reading const file for input constraints {const_path}')
    #     with open(const_path, "r") as const_fp:
    #         all_const=json.load(const_fp)
    # else:
    #     return
    cap_array={}
    #Change covert symmBlock const between caps to common centroid caps
    available_cap_const = []
    if input_const and 'constraints' in input_const:
        all_const = input_const["constraints"]
        for const in input_const["constraints"]:
            if const["const_name"] == 'CC':
                available_cap_const.append(const["cap_name"])
    else:
        input_const = {}
        all_const = []
    logger.debug(f"Searching cap constraints for block {name}, input const: {all_const}")
    for const in all_const:
        if const["const_name"]== "SymmBlock":
            b = [[p["block1"],p["block2"]] for p in const["pairs"] if p["type"]=="sympair"]
            for pair in const["pairs"]:
                if pair["type"]=="sympair":
                    inst=pair["block1"]
                    if inst in graph and graph.nodes[inst]['inst_type'].lower().startswith('cap') \
                        and len (graph.nodes[inst]['ports'])==2: #Not merge user provided const
                        logger.debug("merging cap cc constraints:%s",b)
                        p1,p2=sorted([pair["block1"],pair["block2"]], key=lambda c:graph.nodes[c]['values']["cap"]*1E15)
                        cap_array[p1]={p1:[p1,p2]}
                        pair["type"]="selfsym"
                        pair["block"]= "_".join([p1,p2])
                        del pair["block1"]
                        del pair["block2"]

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
                merge_caps(graph,ctype,cc_caps,cc_cap)
                cc_cap_size[cc_cap]=n_cap
    # updating any symmnet constraint 	
    for id, const in enumerate(all_const):
        if const["const_name"]== "SymmNet":	
            net1 = const['net1']["name"]	
            net2 = const['net2']["name"]	
            existing = ""	
            removed_blocks = [block for block in const['net1']["blocks"] if net1 in graph.nodes() and block['name'] not in graph.nodes()]	
            if removed_blocks:	
                pairs,s1,s2 = symmnet_device_pairs(graph,net1,net2,existing)	
                if pairs:	
                    symmNetj = {"const_name":"SymmNet","axis_dir":"V","net1":s1,"net2":s2}	
                    all_const[id] =symmNetj	
                else:	
                    logger.debug("skipped symmnet on net1 {net1} and net2 {}")

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
            all_const.append(cap_const)
            available_cap_const.append(node)
    input_const["constraints"] = all_const
    logger.debug(f"Identified cap constraints of {name} are {input_const}")

    return input_const
    # if len(all_const["constraints"]) ==0:
    #     os.remove(const_path)
    #     logger.debug("no cap const found: %s",const_path)
    # else:
    #     with open(const_path, 'w') as outfile:
    #         json.dump(all_const, outfile, indent=4)
    #     logger.debug("added cap const: %s",const_path)

# def check_common_centroid(graph,const_path,ports):
#     """
#     Reads common centroid const in generated constraints
#     Merges cc caps as single cap in const-file and netlist
#     Parameters
#     ----------
#     graph : networkx graph
#         Input graph to be modified
#     const_path: pathlib.path
#         Input const file path
#     ports : list
#         Used to check nets which should not be deleted/renamed.
#     Returns
#     -------
#     None.

#     """
#     #new_const_path = const_path.parents[0] / (const_path.stem + '.const_temp')
#     if os.path.isfile(const_path):
#         logger.debug(f'Reading const file for common centroid {const_path}')
#         with open(const_path, "r") as const_fp:
#             all_const=json.load(const_fp)
#     else:
#         return

#     for const in all_const["constraints"]:
#         logger.debug(f"{const}")
#         if  const["const_name"]== "CC" \
#             and isinstance(const["cap_name"],list):
#             logger.debug("Fixing cc constraint for caps:%s",const)
#             caps = const["cap_name"]
#             cc_cap = "_".join(caps)
#             const["cap_name"] = cc_cap
#             name = 'Cap_cc_'+"_".join([str(x) for x in const["size"]])
#             merge_caps(graph,name,caps)

#     with open(const_path, 'w') as outfile:
#         json.dump(all_const, outfile, indent=4)

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
