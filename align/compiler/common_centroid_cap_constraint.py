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


def check_common_centroid(graph,const_path,ports):
    """ Reads available const in input dir
        Merges cc caps as single cap in const-file  and netlist
    """
    cc_pair={}
    #new_const_path = const_path.parents[0] / (const_path.stem + '.const_temp')
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for common centroid {const_path}')
    else:
        return
    with open(const_path, "r") as const_fp:
        all_const=json.load(const_fp)
        #new_const_fp = open(new_const_path, "w")
        for const in all_const["constraints"]:
            if const["const_name"]== "CC" and isinstance(const_name["cap_name"],list):
                logger.info("Fixing cc constraint for caps:%s",const)
                caps = const_name["cap_name"]
                cc_cap = "_".join(caps)
                const_name["cap_name"] = cc_cap
                matched_ports ={}
                for idx,cap in enumerate(caps):
                    #cc_pair.update({cap_block: updated_cap})
                    conn = list(graph.neighbors(cap))
                    matched_ports['MINUS'+str(idx)] = conn[0]
                    matched_ports['PLUS'+str(idx)]= conn[1]
                #line = line.replace(caps_in_line,updated_cap)
                graph, _,_= merge_nodes(
                        graph, 'Cap_cc',caps , matched_ports)
            # new_const_fp.write(line)
            # line=const_fp.readline()
    with open(const_path, 'w') as outfile:
        json.dump(all_const, outfile, indent=4)
    #     os.rename(new_const_path, const_path)
    # else:
    #     logger.debug(f"Couldn't find constraint file {const_path} (might be okay)")
    return(cc_pair)

def WriteCap(graph,input_dir,name,unit_size_cap,all_array):
    const_path = input_dir / (name + '.const.json')
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for common centroid {const_path}')
    else:
        return
    with open(const_path, "r") as const_fp:
        all_const=json.load(const_fp)
    # new_const_path = input_dir / (name + '.const_temp')
    logger.debug(f"writing cap constraints: {const_path} existing array: {all_array}")
    available_cap_const = []
    # if os.path.isfile(const_path):
    #     logger.debug(f'Reading const file for cap {const_path}')
    #     const_fp = open(const_path, "r")
    #     new_const_fp = open(new_const_path, "w")
    #     line = const_fp.readline()
    for const in all_const["constraints"]:
        if const["const_name"]== "SymmBlock":
            b = [[p["block1"],p["block2"]] for p in const["pairs"] if p["type"]=="sympair"]
            #[blocks[blocks.find("{")+1:blocks.find("}")] for blocks in line.split(' , ') if ',' in blocks]
            for pair in const["pairs"]:
                if pair["type"]=="sympair":
                    inst=pair["block1"]
                    if inst in graph and graph.nodes[inst]['inst_type'].lower().startswith('cap'):
                        logger.info("merging cap cc constraints:%s",b)
                        p1,p2=sorted([pair["block1"],pair["block2"]], key=lambda c:graph.nodes[c]['values']["cap"]*1E15)
                        all_array[p1]={p1:[p1,p2]}
                        pair["type"]="selfsym"
                        pair["block"]= "_".join([p1,p2])
    with open(const_path, 'w') as outfile:
        json.dump(all_const, outfile, indent=4)

    # else:
    #     new_const_fp = open(new_const_path, "w")
    #     logger.debug(f"Creating new const file: {new_const_path}")
    logger.debug(f"writing common centroid caps: {all_array}")
    for _,array in all_array.items():
        n_cap=[]
        cc_caps=[]
        logger.debug(f"group1: {array}")
        for _,arr in array.items():
            for ele in arr:
                if ele in graph.nodes() and graph.nodes[ele]['inst_type'].lower().startswith('cap') and \
                    ele not in available_cap_const:
                    if 'cap' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["cap"]*1E15
                    else:
                        size = unit_size_cap
                    n_cap.append( str(ceil(size/unit_size_cap)))
                    cc_caps.append(ele)
        if len(n_cap)>0:
            n_cap, cc_caps =(list(t) for t in  zip(*sorted(zip(n_cap, cc_caps))))
            available_cap_const = available_cap_const+ cc_caps
            unit_block_name = '} , {Cap_' + str(unit_size_cap) + 'f} , {nodummy} )'
            cap_line = "\nCC ( {"+','.join(cc_caps)+"} , {"+','.join(n_cap)+unit_block_name
            logger.debug("Cap constraint"+cap_line)
            #const_fp.write(cap_line)


    for node, attr in graph.nodes(data=True):
        if attr['inst_type'].lower().startswith('cap')  and node not in available_cap_const:
            if 'cap' in attr['values'].keys():
                size = attr['values']["cap"]*1E15
            else:
                size = unit_size_cap
            n_cap = ceil(size/unit_size_cap)
            if n_cap > 128:
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
    const_fp.close()
    if os.stat(const_path).st_size ==0:
        os.remove(const_path)
        logger.info("no cap const found: %s",const_path)
    else:
        #os.rename(const_path, const_path)
        logger.info("added cap const: %s",const_path)
