# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""
from .util import convert_to_unit
from .merge_nodes import merge_nodes

from collections import Counter

import logging
logger = logging.getLogger(__name__)
def compare_nodes(G,match_pair,traverced,nodes1,nodes2):
    #logger.debug("comparing %s,%s, traversed %s %s",nodes1,nodes2,traverced,list(G.neighbors(nodes1)))
    #logger.debug("Comparing node: %s %s , traversed:%s",nodes1,nodes2,traverced)
    #match_pair={}
    #logger.debug("comparing %s, %s ",G.nodes[nodes1],G.nodes[nodes2])
    if 'net' in G.nodes[nodes1]['inst_type'] and \
        G.nodes[nodes1]['net_type'] == 'external':
            port=True
    else:
        port = False
    if (not port and len(list(G.neighbors(nodes1))) <=2 and \
        set(G.neighbors(nodes1)) == set(G.neighbors(nodes2)) ) or\
        (port and len(list(G.neighbors(nodes1))) ==1):
        for node1 in list(G.neighbors(nodes1)):
            if node1 not in traverced:
                logger.debug(node1)
                #print(nodes1,nodes2,list(G.neighbors(nodes1)),list(G.neighbors(nodes2)))
                match_pair[node1]=node1
                traverced.append(node1)
                compare_nodes(G,match_pair,traverced,node1,node1)
    for node1 in list(G.neighbors(nodes1)):
        if node1 not in traverced and \
                node1 not in match_pair.keys():
            for node2 in list(G.neighbors(nodes2)):
                if node1 != node2 and node2 not in traverced:
                    if compare_node(G,node1,node2):
                        if G.get_edge_data(nodes1,node1)['weight'] == G.get_edge_data(nodes2,node2)['weight']:
                            #match_pair[nodes1][1].append(node1)
                            #match_pair[nodes2][2].append(node2)
                            match_pair[node1]=node2
                            #print(node1,node2)
                            traverced.append(node1)
                            traverced.append(node2)
                            compare_nodes(G,match_pair,traverced,node1,node2)
    return match_pair
def compare_node(G,node1,node2):
    if G.nodes[node1]["inst_type"]=="net" and \
            G.nodes[node2]["inst_type"]=="net" and \
            len(list(G.neighbors(node1)))==len(list(G.neighbors(node2))) and \
            G.nodes[node1]["net_type"] == G.nodes[node2]["net_type"]:
        #logger.debug("comparing_nodes, %s %s True",node1,node2)
        return True
    elif (G.nodes[node1]["inst_type"]==G.nodes[node2]["inst_type"] and
        'values' in G.nodes[node1].keys() and
         G.nodes[node1]["values"]==G.nodes[node2]["values"] and
        len(list(G.neighbors(node1)))==len(list(G.neighbors(node2)))):
        #logger.debug("comparing_nodes, %s %s True",node1,node2)
        return True
    else:
        logger.debug("comparing_nodes, %s %s False",node1,node2)
        return False
def matching_groups(G,level1):
    similar_groups=[]
    logger.debug("matching groups for all neighbors: %s", level1)
    for l1_node1 in level1:
        for l1_node2 in level1:
            if l1_node1!= l1_node2 and compare_node(G,l1_node1,l1_node2):
                found_flag=0
                #logger.debug("similar_group %s",similar_groups)
                #print(l1_node1,l1_node2)
                for index, sublist in enumerate(similar_groups):
                    if l1_node1 in sublist and l1_node2 in sublist:
                        found_flag=1
                        break
                    if l1_node1 in sublist:
                        similar_groups[index].append(l1_node2)
                        found_flag=1
                        #print("found match")

                        break
                    elif l1_node2 in sublist:
                        similar_groups[index].append(l1_node1)
                        found_flag=1
                        #print("found match")
                        break
                if found_flag==0:
                    similar_groups.append([l1_node1,l1_node2])
    return similar_groups

def trace_template(graph, similar_node_groups,visited,template,array):
    next_match={}
    for source,groups in similar_node_groups.items():
        next_match[source]=[]
        for node in groups:
            #print(node)
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            #level1=[l1 for l1 in level_1a if l1 not in visited]
            next_match[source] +=level1
            visited +=level1
        if len(next_match[source])==0:
            del next_match[source]

    if len(next_match.keys())> 0 and match_branches(graph,next_match) :
        for source in array.keys():
            if source in next_match.keys():
                array[source]+=next_match[source]
        template +=next_match[list(next_match.keys())[0]]
        logger.debug("found matching level: %s,%s",template,similar_node_groups)
        trace_template(graph, next_match,visited,template,array)


def match_branches(graph,nodes_dict):
    #print("matching branches",nodes_dict)
    #match_pair={}
    nbr_values = {}
    for node, nbrs in nodes_dict.items():
        #super_dict={}
        super_list=[]
        for nbr in nbrs:
            #print("checking nbr",nbr,graph.nodes[nbr])
            if graph.nodes[nbr]['inst_type']== 'net':
                super_list.append('net')
                super_list.append(graph.nodes[nbr]['net_type'])
            else:
                super_list.append(graph.nodes[nbr]['inst_type'])
                for v in graph.nodes[nbr]['values'].values():
                    #super_dict.setdefault(k,[]).append(v)
                    #print("value",k,v
                    super_list.append(v)
        nbr_values[node]=Counter(super_list)
    _,main=nbr_values.popitem()
    for node, val in nbr_values.items():
        if val == main:
            #print("found values",list(val.elements()))
            continue
        else:
            return False
    return True

def FindArray(graph,input_dir,name):
    templates = {}
    array_of_node = {}
    visited =[]
    all_array = {}

    for node, attr in graph.nodes(data=True):
        #print("node data",graph.nodes[node])
        if  'net' in attr["inst_type"] and len(list(graph.neighbors(node)))>4:
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            array_of_node[node]=matching_groups(graph,level1)
            logger.debug("finding array:%s,%s",node,array_of_node[node])
            if len(array_of_node[node]) > 0 and len(array_of_node[node][0])>1:
                similar_node_groups = {}
                for el in array_of_node[node][0]:
                    similar_node_groups[el]=[el]
                templates[node]=[list(similar_node_groups.keys())[0]]
                visited=array_of_node[node][0]+[node]
                array=similar_node_groups
                trace_template(graph,similar_node_groups,visited,templates[node],array)
                logger.debug("similar groups final, %s",array)
                all_array[node]=array
    return all_array
                #match_branches(graph,nodes_dict)

def CopyConstFile(name, input_dir, working_dir):
    # Copy const file to working directory if needed
    input_const_file = (input_dir / (name + '.const'))
    const_file = (working_dir / (name + '.const'))
    if input_const_file.exists() and input_const_file.is_file():
        if const_file == input_const_file:
            (input_dir / (name + '.const.old')).write_text(input_const_file.read_text())
        else:
            const_file.write_text(input_const_file.read_text())
    return const_file

def WriteConst(graph, input_dir, name, ports, stop_points):

    const_file = (input_dir / (name + '.const'))

    #check_common_centroid(graph,const_file,ports)
    logger.debug("writing constraints: %s",const_file)
    #const_fp.write(str(ports))
    #const_fp.write(str(graph.nodes()))
    traverced =stop_points
    all_match_pairs={}
    for port1 in sorted(ports):
        if port1 in graph.nodes() and port1 not in traverced:
            for port2 in sorted(ports):
                if port2 in graph.nodes() and sorted(ports).index(port2)>=sorted(ports).index(port1) and port2 not in traverced:
            #while len(list(graph.neighbors(port)-set(traverced)))==1:
            #nbr = list(graph.neighbors(port))
                    pair ={}
                    traverced.append(port1)
                    compare_nodes(graph, pair, traverced, port1, port2)
                    if pair:
                        all_match_pairs.update(pair)
                        logging.info("Symmetric blocks found: %s",pair)
    existing_SymmBlock =[]
    existing_SymmNet = False

    # Read contents
    logger.info("input const file: %s", const_file)
    if const_file.exists() and const_file.is_file():
        with open(const_file) as f:
            for content in f:
                logger.info("line %s",content)
                if 'SymmBlock' in content:
                    existing_SymmBlock+=content
                    logger.info("symmblock found %s",content)
                elif 'SymmNet' in content:
                    existing_SymmNet = True
    del_existing=[]
    for key, value in all_match_pairs.items():
        if key in existing_SymmBlock or value in existing_SymmBlock:
            del_existing.append(key)
    logging.info("matching pairs:%s existing %s",all_match_pairs,existing_SymmBlock)
    logging.info("removing existing symmblocks:%s",del_existing)
    for nodes in del_existing:
        del all_match_pairs[nodes]

    const_fp = open(const_file, 'a+')
    if len(list(all_match_pairs.keys()))>0:
        symmBlock = "SymmBlock ("
        for key, value in all_match_pairs.items():
            if key in stop_points:
                continue
            if graph.nodes[key]["inst_type"]!="net" and \
                key not in symmBlock and value not in symmBlock and \
                'Dcap' not in graph.nodes[key]["inst_type"] :
                if key !=value:
                    symmBlock = symmBlock+' {'+key+ ','+value+'} ,'
            elif 'Dcap' not in graph.nodes[key]["inst_type"] :
                if len(connection(graph,key))<3 and len(connection(graph,key))>1:
                    symmNet = "SymmNet ( {"+key+','+','.join(connection(graph,key)) + \
                            '} , {'+value+','+','.join(connection(graph,value)) +'} )\n'
                    if not existing_SymmNet:
                        const_fp.write(symmNet)


        for key, value in all_match_pairs.items():
            if graph.nodes[key]["inst_type"]!="net" and 'Dcap' not in graph.nodes[key]["inst_type"] :
                if key ==value and key not in symmBlock:
                    symmBlock = symmBlock+' {'+key+ '} ,'

        symmBlock = symmBlock[:-1]+')\n'
        if not existing_SymmBlock:
            const_fp.write(symmBlock)
        const_fp.close()
