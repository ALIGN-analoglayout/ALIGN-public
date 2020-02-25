# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""

from collections import Counter

import logging
logger = logging.getLogger(__name__)
def compare_nodes(G,match_pair,traversed,node1,node2, ports_weight):
    """

    Parameters
    ----------
    G : networkx graph
        reduced hierarchical circuit graph.
    match_pair : dict type
        stores list of matched pairs.
    traversed : list of nodes already traversed, to avoid retracing
    node1,node2 : start points to create trees for comparison
    ports_weight :TYPE. dict
        dictionary of port weights
    Returns
    -------
    match_pair : dict type
        stores list of matched pairs.

    """
    logger.debug("comparing %s,%s,%s%s, traversed %s %s",node1,G.nodes[node1],node2,G.nodes[node2],traversed,list(G.neighbors(node1)))

    """ 
    Traversing single branch for symmetry
    condition 1, Single branch: both ports/ nets are same and connected to two or more ports
    condition 2, Converging branch: two nets are diffrent but connected to single device node
    condition 3: Two parallel branches
    """
    #if not port and len(list(G.neighbors(node1))) <=2 or \
    #   (port and set(G.neighbors(node1)) == set(G.neighbors(node2)) ) :
    if node1 == node2:
        nbrs = list(set(G.neighbors(node1))- set(traversed))
        SD_nbrs= [nbr for nbr in nbrs if G.get_edge_data(node1, nbr)['weight'] !=2]
        """
        TBD: filter based on primitive constraints
        Right now will try to figure out S/D paths
        """
        if len(nbrs) ==1:
            logger.debug(f"traversing single path from port {node1} ")
            #match_pair[node1]=node1 
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,nbrs[0],nbrs[0],ports_weight)
        elif len(nbrs) ==2:
            logger.debug(f"diverging branch from single branch {node1} ")
            match_pair[node1]=node1
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,nbrs[0],nbrs[1],ports_weight)
        elif len(SD_nbrs) ==1:
            logger.debug(f"traversing single path from device {node1} ")
            match_pair[node1]=node1 
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,SD_nbrs[0],SD_nbrs[0],ports_weight)            
        elif len(SD_nbrs) ==2:
            logger.debug(f"diverging S/D branch from single branch {node1} {SD_nbrs} ")
            match_pair[node1]=node1
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,SD_nbrs[0],SD_nbrs[1],ports_weight)            
        else:
            logger.debug(f" multiple blocks symmetry to be done {set(G.neighbors(node1))} {set(traversed) }{nbrs} {SD_nbrs}")
            logger.debug(f"nbr weights: {nbrs} {[G.get_edge_data(node1, nbr)['weight'] for nbr in nbrs  ]}")
            
    elif (set(G.neighbors(node1)) - set(traversed) == set(G.neighbors(node2)) - set(traversed)):
        nbrs= list(set(G.neighbors(node1)) - set(traversed))
        logger.debug(f"traversing converging branch {node1} {node2}")
        match_pair[node1]=node2
        traversed.extend([node1,node2])
        for nbr1 in nbrs:
            for nbr2 in nbrs:
                compare_nodes(G,match_pair,traversed,nbr1,nbr2,ports_weight)

    elif compare_node(G,node1,node2,ports_weight):
        """
        Traversing binary branch
        """
        logger.debug(f"traversing binary branch {node1} {node2}")
        match_pair[node1]=node2
        traversed.extend([node1,node2])       
        for nbr_node1 in list(G.neighbors(node1)):
            if nbr_node1 not in traversed and \
                    nbr_node1 not in match_pair.keys():
                for nbr_node2 in list(G.neighbors(node2)):
                    if nbr_node1 != nbr_node2 and nbr_node2 not in traversed:
                        compare_nodes(G,match_pair,traversed,nbr_node1,nbr_node2,ports_weight)

    return match_pair
def compare_node(G,node1,node2,ports_weight):
    logger.debug("comparing_nodes, %s %s ",node1,node2)
   
    if G.nodes[node1]["inst_type"]=="net" and \
        G.nodes[node2]["inst_type"]=="net" and \
        len(list(G.neighbors(node1)))==len(list(G.neighbors(node2))) and \
        G.nodes[node1]["net_type"] == G.nodes[node2]["net_type"]:
            
        if G.nodes[node1]["net_type"] == 'external':
            if ports_weight[node1] == ports_weight[node2]:
                logger.debug("True")
                return True
        elif G.nodes[node1]["net_type"] == 'internal':
            weight1=[]
            for nbr in list(G.neighbors(node1)):
                weight1.append(G.get_edge_data(node1, nbr)['weight'])            
            weight2=[]
            for nbr in list(G.neighbors(node2)):
                weight2.append(G.get_edge_data(node2, nbr)['weight'])
            if weight2==weight1:
                logger.debug("True")
                return True
    elif (G.nodes[node1]["inst_type"]==G.nodes[node2]["inst_type"] and
        'values' in G.nodes[node1].keys() and
         G.nodes[node1]["values"]==G.nodes[node2]["values"] and
        len(list(G.neighbors(node1)))==len(list(G.neighbors(node2)))):
        logger.debug(" True")
        return True
    else:
        logger.debug(" False")
        return False
def matching_groups(G,level1,ports_weight):
    similar_groups=[]
    logger.debug("matching groups for all neighbors: %s", level1)
    for l1_node1 in level1:
        for l1_node2 in level1:
            if l1_node1!= l1_node2 and compare_node(G,l1_node1,l1_node2,ports_weight):
                found_flag=0
                #logger.debug("similar_group %s",similar_groups)
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
    for source,groups in similar_node_groups.items():
        next_match[source]=[]
        for node in groups:
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
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
    nbr_values = {}
    for node, nbrs in nodes_dict.items():
        #super_dict={}
        super_list=[]
        for nbr in nbrs:
            if graph.nodes[nbr]['inst_type']== 'net':
                super_list.append('net')
                super_list.append(graph.nodes[nbr]['net_type'])
            else:
                super_list.append(graph.nodes[nbr]['inst_type'])
                for v in graph.nodes[nbr]['values'].values():
                    #super_dict.setdefault(k,[]).append(v)
                    super_list.append(v)
        nbr_values[node]=Counter(super_list)
    _,main=nbr_values.popitem()
    for node, val in nbr_values.items():
        if val == main:
            continue
        else:
            return False
    return True

def FindArray(graph,input_dir,name,ports_weight):
    templates = {}
    array_of_node = {}
    visited =[]
    all_array = {}

    for node, attr in graph.nodes(data=True):
        if  'net' in attr["inst_type"] and len(list(graph.neighbors(node)))>4:
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            array_of_node[node]=matching_groups(graph,level1,ports_weight)
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

def WriteConst(graph, input_dir, name, ports, ports_weight, stop_points):
    const_file = (input_dir / (name + '.const'))
    logger.debug("writing constraints: %s",const_file)
    logger.debug(f"ports weight: {ports_weight} stop_points : {stop_points}")

    traversed =stop_points.copy()
    all_match_pairs={}
    for port1 in sorted(ports):
        if port1 in graph.nodes() and port1 not in traversed:
            for port2 in sorted(ports):
                traversed =stop_points.copy()
                if port2 in graph.nodes() and port2 not in traversed \
                    and ports_weight[port1] == ports_weight[port2] \
                    and sorted(ports).index(port2)>=sorted(ports).index(port1):
                    pair ={}
                    traversed.append(port1)
                    compare_nodes(graph, pair, traversed, port1, port2,ports_weight)
                    if pair:
                        all_match_pairs[port1+port2]=pair                         
                        logging.info("Symmetric blocks found: %s",pair)


    # Read contents of input constraint file
    """
    Check if there are any other constraints except cap constraints
    No constraints are written in case constraints are provided
    """
    logger.info("input const file: %s", const_file)
    if const_file.exists() and const_file.is_file():
        with open(const_file) as f:
            for content in f:
                logger.info("line %s",content)
                if 'SymmBlock' in content or 'SymmNet' in content:
                    return

                    
    written_symmetries = 'all'
    const_fp = open(const_file, 'a+')
    for pairs in sorted(all_match_pairs.values(), key=lambda k: len (k.keys()), reverse=True):
        print(pairs,written_symmetries)
        symmBlock='\nSymmBlock ('
        for key, value in pairs.items():    
            if key in stop_points or key in written_symmetries or value in written_symmetries :
                continue
            if graph.nodes[key]["inst_type"]!="net" and \
                'Dcap' not in graph.nodes[key]["inst_type"] :
                if key !=value:
                    symmBlock += ' {'+key+ ','+value+'} ,'
                else:
                    symmBlock +=' {' + key +'} ,'
                written_symmetries += symmBlock
            elif 'Dcap' not in graph.nodes[key]["inst_type"] :
                nbrs_key = [graph.get_edge_data(key, nbr)['weight'] for nbr in list(set(graph.neighbors(key)))]
                nbrs_val = [graph.get_edge_data(value, nbr)['weight'] for nbr in list(set(graph.neighbors(value)))]
                if nbrs_key != nbrs_val:
                    logger.info(f"filtering nets which came due to S/D traversal {key} {value}{nbrs_key} {nbrs_val}")
                if len(connection(graph,key))<=3 and key!=value  :
                    symmNet = "\nSymmNet ( {"+key+','+','.join(connection(graph,key)) + \
                            '} , {'+value+','+','.join(connection(graph,value)) +'} )'
                    const_fp.write(symmNet)
                    written_symmetries += ' '+ key+ ','+value
                else:
                    logger.debug(f"TBD:multiple connections of net need proper handle {key}")
        if len(symmBlock) > 13:
            symmBlock = symmBlock[:-1]+')'
            const_fp.write(symmBlock)
    const_fp.close()

def connection(graph,net):
    conn =[]
    for nbr in list(graph.neighbors(net)):
        try:
            if "ports_match" in graph.nodes[nbr]:
                #logger.debug("ports match:%s %s",net,graph.nodes[nbr]["ports_match"].items())
                idx=list(graph.nodes[nbr]["ports_match"].values()).index(net)
                conn.append(nbr+'/'+list(graph.nodes[nbr]["ports_match"].keys())[idx])
            elif "connection" in graph.nodes[nbr]:
                #logger.debug("connection:%s%s",net,graph.nodes[nbr]["connection"].items())
                idx=list(graph.nodes[nbr]["connection"].values()).index(net)
                conn.append(nbr+'/'+list(graph.nodes[nbr]["connection"].keys())[idx])
        except ValueError:
            logger.debug("internal net")
    if graph.nodes[net]["net_type"]=="external":
        conn.append(net)
    return conn
