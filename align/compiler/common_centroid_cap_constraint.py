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
logger = logging.getLogger(__name__)


def check_common_centroid(graph,const_path,ports):
    """ Reads available const in input dir
        Fix cc cap in const and netlist
    """
    cc_pair={}
    new_const_path = const_path.parents[0] / (const_path.stem + '.const_temp')
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for common centroid {const_path}')
        const_fp = open(const_path, "r")
        new_const_fp = open(new_const_path, "w")
        line = const_fp.readline()
        while line:
            logger.info("checking cc constraint for caps:%s",line)
            if line.startswith("CC") and len(line[line.find("{")+1:line.find("}")].split(','))>=2:
                caps_in_line = line[line.find("{")+1:line.find("}")]
                updated_cap = caps_in_line.replace(',','_')
                cap_blocks = caps_in_line.strip().split(',')
                matched_ports ={}
                for idx,cap_block in enumerate(cap_blocks):
                    cc_pair.update({cap_block: updated_cap})
                    conn = list(graph.neighbors(cap_block))
                    matched_ports['MINUS'+str(idx)] = conn[0]
                    matched_ports['PLUS'+str(idx)]= conn[1]
                line = line.replace(caps_in_line,updated_cap)
                graph, _ = merge_nodes(
                        graph, 'Cap_cc',cap_blocks , matched_ports)
            new_const_fp.write(line)
            line=const_fp.readline()

        const_fp.close()
        new_const_fp.close()
        os.rename(new_const_path, const_path)
    else:
        logger.debug(f"Couldn't find constraint file {const_path} (might be okay)")

    return(cc_pair)

def WriteCap(graph,input_dir,name,unit_size_cap,all_array):
    const_path = input_dir / (name + '.const')
    new_const_path = input_dir / (name + '.const_temp')
    logger.debug(f"writing cap constraints: {new_const_path}")
    available_cap_const = []
    if os.path.isfile(const_path):
        logger.debug(f'Reading const file for cap {const_path}')
        const_fp = open(const_path, "r")
        new_const_fp = open(new_const_path, "w")
        line = const_fp.readline()
        while line:
            logger.info("const line :%s",line)
            if line.startswith("CC"):
                caps_in_line = line[line.find("{")+1:line.find("}")]
                cap_blocks = caps_in_line.strip().split(',')
                available_cap_const = available_cap_const+cap_blocks
            elif line.startswith("SymmBlock"):
                blocks_in_line = [blocks[blocks.find("{")+1:blocks.find("}")] for blocks in line.split(' , ') if ',' in blocks]
                logger.info("place symmetrical cap as CC:%s",blocks_in_line)
                for pair in blocks_in_line:
                    p1,p2=pair.split(',')
                    if graph.nodes[p1]['inst_type'].lower().startswith('cap'):
                        all_array[p1]={p1:[p1,p2]}
                        line=line.replace(' {'+pair+'} ','').replace('(,','(').replace(',)',')').replace(',,',',')
            new_const_fp.write(line)
            logger.debug(f"cap const {line}")
            line=const_fp.readline()
        const_fp.close()
    else:
        new_const_fp = open(new_const_path, "w")
        logger.debug(f"Creating new const file: {new_const_path}")
    logger.debug(f"writing common centroid caps: {all_array}")
    for _,array in all_array.items():
        n_cap=[]
        cc_caps=[]
        logger.debug(f"group1: {array}")
        for _,arr in array.items():
            for ele in arr:
                if graph.nodes[ele]['inst_type'].lower().startswith('cap') and \
                    ele not in available_cap_const:
                    if 'cap' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["cap"]*1E15
                    elif 'c' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["c"]*1E15
                    else:
                        size = unit_size_cap
                    n_cap.append( str(ceil(size/unit_size_cap)))
                    cc_caps.append(ele)
        if len(n_cap)>0:
            available_cap_const = available_cap_const+ cc_caps
            unit_block_name = '} , {Cap_' + str(unit_size_cap) + 'f} )'
            cap_line = "\nCC ( {"+','.join(cc_caps)+"} , {"+','.join(n_cap)+unit_block_name
            logger.debug("Cap constraint"+cap_line)
            new_const_fp.write(cap_line)


    for node, attr in graph.nodes(data=True):
        if attr['inst_type'].lower().startswith('cap')  and node not in available_cap_const:
            if 'cap' in attr['values'].keys():
                size = attr['values']["cap"]*1E15
            elif 'c' in attr['values'].keys():
                size = attr['values']["c"]*1E15
            else:
                size = unit_size_cap
            n_cap = ceil(size/unit_size_cap)
            if n_cap > 128:
                unit_block_name = '} , {Cap_' + str(int(round(size,1))) + 'f} )'
                n_cap=1
            else:
                unit_block_name = '} , {Cap_' + str(unit_size_cap) + 'f} )'
            cap_line = "\nCC ( {"+node+"} , {"+str(n_cap)+unit_block_name
            logger.debug("Cap constraint"+cap_line)
            new_const_fp.write(cap_line)
            available_cap_const.append(node)
    new_const_fp.close()
    if os.stat(new_const_path).st_size ==0:
        os.remove(new_const_path)
        logger.info("no cap const found: %s",new_const_path)
    else:
        os.rename(new_const_path, const_path)
        logger.info("added cap const: %s",const_path)