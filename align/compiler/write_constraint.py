# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""

from collections import Counter
from itertools import combinations,combinations_with_replacement
from .merge_nodes import merge_nodes

import logging
logger = logging.getLogger(__name__)

def create_hierarchy(graph,node,traversed,ports_weight):
    hier_of_node ={}
    
    level1=list(set(graph.neighbors(node))- set(traversed))
    
    hier_of_node[node]=matching_groups(graph,level1,None)
    logger.debug(f"new hierarchy points {hier_of_node} {level1}")

    if len(hier_of_node[node]) > 0:
        for group in hier_of_node[node]:
            if len(group)>0:
                templates={}
                similar_node_groups = {}
                for el in group:
                    similar_node_groups[el]=[el]
                templates[node]=[el]
                visited=group+[node]
                array=similar_node_groups.copy()
                trace_template(graph,similar_node_groups,visited,templates[node],array)
                logger.debug("similar groups final, %s",array)
                
        all_inst = []
        if array and len(array.values())>1 and len(list(array.values())[0])>1:
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
            h_ports_weight={}
            for inst in  all_inst:
                for node_hier in list(set(graph.neighbors(inst))):
                    if graph.nodes[node_hier]['inst_type']== 'net':
                        if (set(graph.neighbors(node_hier))- set(all_inst)):
                            matched_ports[node_hier]=node_hier
                            h_ports_weight[node_hier] = []
                            for nbr in list(graph.neighbors(node_hier)):
                                h_ports_weight[node_hier].append(graph.get_edge_data(node_hier, nbr)['weight'])
                       
            logger.debug(f"creating a new hierarchy for {node}, {all_inst}, {matched_ports}")
            graph, subgraph,_ = merge_nodes(
                    graph, 'dummy_hier_'+node,all_inst , matched_ports)
            hier_of_node[node]={
                        "name": 'dummy_hier_'+node,
                        "graph": subgraph,
                        "ports": list(matched_ports.keys()),
                        "ports_match": matched_ports,
                        "ports_weight": h_ports_weight,
                        "size": len(subgraph.nodes())
                    }
        return hier_of_node

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
def check_convergence(match:dict):
    vals=[]
    for val in match.values():
        if set(val).intersection(vals):
            return False
        else:
            vals+=val
            
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

def FindArray(graph,input_dir,name,ports_weight):
    templates = {}
    array_of_node = {}
    visited =[]
    all_array = {}

    for node, attr in graph.nodes(data=True):
        if  'net' in attr["inst_type"] and len(list(graph.neighbors(node)))>2:
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            array_of_node[node]=matching_groups(graph,level1,ports_weight)
            logger.debug("finding array:%s,%s,%s",node,array_of_node[node],level1)
            if len(array_of_node[node]) > 0 and len(array_of_node[node][0])>1:
                for group in array_of_node[node]:
                    similar_node_groups = {}
                    for el in group:
                        similar_node_groups[el]=[el]
                    templates[node]=[el]
                    visited=group+[node]
                    array=similar_node_groups.copy()
                    trace_template(graph,similar_node_groups,visited,templates[node],array)
                    logger.debug("similar groups final, %s",array)
                    all_array[node]=array
    return all_array

def matching_groups(G,level1,ports_weight):
    similar_groups=[]
    logger.debug("matching groups for all neighbors: %s", level1)
    for l1_node1,l1_node2 in combinations(level1, 2):
        if compare_node(G,l1_node1,l1_node2,ports_weight):
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
def find_unique_matching_branches(G,nbrs1,nbrs2,ports_weight):
    match={}
    for node1 in nbrs1:
        for node2 in nbrs2:
            if compare_node(G, node1, node2, ports_weight):
                if node1 in match:
                    return False
                else:
                    match[node1]=node2
        if node1 not in match:
            return False
    return match
        
    
def compare_node(G,node1:str,node2:str ,ports_weight):
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
    logger.debug("comparing_nodes, %s %s %s %s",node1,node2,list(G.neighbors(node1)),list(G.neighbors(node2)))
    nbrs1= [nbr for nbr in G.neighbors(node1) if G.get_edge_data(node1, nbr)['weight'] !=2]
    nbrs2= [nbr for nbr in G.neighbors(node2) if G.get_edge_data(node2, nbr)['weight'] !=2]

    # Add some heuristic here in future
    
    nbrs1_type= sorted([G.nodes[nbr]["inst_type"] for nbr in nbrs1]) + [G.nodes[node1]["inst_type"]]
    nbrs2_type= sorted([G.nodes[nbr]["inst_type"] for nbr in nbrs2]) + [G.nodes[node2]["inst_type"]]
    if nbrs1_type != nbrs2_type:
        logger.debug(f"type mismatch {nbrs1}:{nbrs1_type} {nbrs2}:{sorted(nbrs2_type)}")
        return False
    if G.nodes[node1]["inst_type"]=="net": 
        if G.nodes[node1]["net_type"] == G.nodes[node2]["net_type"] == 'external':
            if not ports_weight:
                return True
            elif sorted(ports_weight[node1]) == sorted(ports_weight[node2]):
                logger.debug("True")
                return True
            else:
                logger.debug(f'external port weight mismatch {ports_weight[node1]},{ports_weight[node2]}')
                return False
        elif G.nodes[node1]["net_type"] == 'internal':
            weight1=[G.get_edge_data(node1, nbr)['weight'] for nbr in nbrs1]
            weight2=[G.get_edge_data(node2, nbr)['weight'] for nbr in nbrs2]
            if weight2==weight1:
                logger.debug("True")
                return True
            else:
                logger.debug(f'internal port weight mismatch {weight1},{weight2}')
                return False
    else: 
        if 'values' in G.nodes[node1].keys() and \
        G.nodes[node1]["values"]==G.nodes[node2]["values"]:
            logger.debug(" True")
            return True
        else:
            logger.debug(" False, value mismatch")
            return False


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
    logger.debug("comparing %s,%s, traversed %s",node1,node2,traversed)
    nbrs1 = set(G.neighbors(node1)) - set(traversed)
    nbrs2 = set(G.neighbors(node2)) - set(traversed)
    logger.debug(f"first node1:{node1},property: {G.nodes[node1]},neigbors1: {nbrs1}")
    logger.debug(f"second node2:{node2},property: {G.nodes[node2]},neigbors2: {nbrs2}")
    if not nbrs1 or not nbrs2:
        if compare_node(G, node1, node2, ports_weight):
            match_pair[node1]=node2
        logger.debug("no new neihbours, returning recursion")
        return
    #Traversing single branch for symmetry
    #condition 1, Single branch: both ports/ nets are same and connected to two or more ports
    #condition 2, Converging branch: two nets are diffrent but connected to single device node
    #condition 3: Two parallel branches
    #condition 3: Two branches with multiple fanout will create new start points
    #condition 4: Diverging branch with more than 2 fanout, check all pairs
    
    #if not port and len(list(G.neighbors(node1))) <=2 or \
    #   (port and set(G.neighbors(node1)) == set(G.neighbors(node2)) ) :
    
    if node1 == node2:
        if node1 in match_pair.keys() or node1 in match_pair.values():
            logger.debug("avoid existing  pair wise symmetry")
            return
        logger.debug(f"single node {node1}, nbrs {nbrs1}, nbr_weight {[G.get_edge_data(node1,nbr) for nbr in nbrs1]}")
        SD_nbrs= [nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['weight'] !=2]
        ## TBD: filter based on primitive constraints
        ## Right now will try to figure out S/D paths
        if len(SD_nbrs) ==0:
            logger.debug(f"No SD paths found to traverse")
        elif len(SD_nbrs) ==1:
            logger.debug(f"traversing single S/D path ")
            match_pair[node1]=node1 
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,SD_nbrs[0],SD_nbrs[0],ports_weight)            
        elif len(SD_nbrs) ==2:
            logger.debug(f"diverging S/D branch from single branch {SD_nbrs} ")
            match_pair[node1]=node1
            traversed.append(node1)
            compare_nodes(G,match_pair,traversed,SD_nbrs[0],SD_nbrs[1],ports_weight)            
        else:        
            logger.debug(f" multiple nodes diverging {nbrs1} {SD_nbrs}")
            logger.debug(f"nbr weights: {SD_nbrs} {[G.get_edge_data(node1, nbr)['weight'] for nbr in SD_nbrs  ]}")
            match_pair[node1]=node1
            traversed.append(node1)
            for nbr1,nbr2 in combinations_with_replacement(set(SD_nbrs)-set(traversed), 2):
                logger.debug(f"recursive call from single branch {nbr1} {nbr2}")
                compare_nodes(G,match_pair,traversed.copy(),nbr1,nbr2,ports_weight)
                        
    elif nbrs1 == nbrs2:
        logger.debug(f"traversing converging branch")
        match_pair[node1]=node2
        traversed+=[node1,node2]
        nbrs1=nbrs1-set([node1,node2])
        logger.debug(f"all non traversed neighbours: {nbrs1}")
        for nbr1,nbr2 in combinations_with_replacement(nbrs1,2):
            logger.debug(f"recursive call from converged branch {nbr1} {nbr2}")
            compare_nodes(G,match_pair,traversed.copy(),nbr1,nbr2,ports_weight)

    elif compare_node(G,node1,node2,ports_weight):
        match_pair[node1]=node2
        traversed+=[node1,node2]
        logger.info(f"Traversing parallel branches")
        nbrs1_wt = [G.get_edge_data(node1, nbr)['weight'] for nbr in nbrs1]
        nbrs2_wt = [G.get_edge_data(node2, nbr)['weight'] for nbr in nbrs2]
        unique_match=find_unique_matching_branches(G,nbrs1,nbrs2,ports_weight)
        if len(nbrs1) ==1 and len(nbrs2)==1:
            logger.debug(f"traversing binary branch")
            compare_nodes(G,match_pair,traversed,nbrs1.pop(),nbrs2.pop(),ports_weight)
        elif unique_match:
            logger.debug(f'traversing unique matches {unique_match}')
            match_pair[node1]=node2
            traversed+=[node1,node2]
            for nbr1,nbr2 in unique_match.items():
                logger.debug(f"recursive call from binary {node1}:{node2} to {nbr1}:{nbr2}")
                compare_nodes(G,match_pair,traversed.copy(),nbr1,nbr2,ports_weight)
        elif len(nbrs1_wt)>len(set(nbrs1_wt))>1 and len(nbrs2_wt)>len(set(nbrs2_wt))>1:
            logger.debug(f"setting new start points {node1} {node2}")
            match_pair[node1]=node2
            if "start_point" in match_pair.keys():
                match_pair["start_point"]+=[node1,node2]
            else:
                match_pair["start_point"]=[node1,node2]
        else:
            logger.debug(f"end all traversal from binary branch {node1} {node2}")
        
    else:
        logger.debug(f"end of recursion branch, matches {match_pair}")

def recursive_start_points(G,all_match_pairs,traversed,node1,node2, ports_weight):
    logger.debug(f"symmetry start point {node1} {node2}")
    pair ={}
    compare_nodes(G, pair, traversed, node1, node2,ports_weight)

    if "start_point" in pair:
        hier_start_points=pair["start_point"]    
        del pair["start_point"]
    if not pair:
        logger.debug(f"Non symmetrical branches {node1}:{node2}")
        return                  
    else:
        logging.info(f"symmetric blocks found: {pair}")      
        all_match_pairs[node1+node2]=pair                         
    try: 
        for sp in hier_start_points:
            logger.debug(f"starting new node from binary branch:{sp} {hier_start_points} traversed {traversed}")
            if sp not in G.nodes():
                continue
            multifanout = create_hierarchy(G,sp,traversed,ports_weight)
            if  multifanout and isinstance(multifanout[sp], list):
                logger.debug(f"only one level matched so putting as align block:{multifanout[sp]}")
                all_match_pairs[node1+node2+'_align']=multifanout[sp]
            elif multifanout and isinstance(multifanout[sp], dict):
                logger.debug(f"more than one depth matched so creating new hierarchy :{multifanout[sp]}")
                #all_match_pairs[node1+node2+"_align_hier_"+sp]=multifanout[sp]
                traversed+=[node1,node2]
                all_match_pairs[sp+'_new_hier']=multifanout[sp]
                
                logger.debug("new hier list %s %s",sp, multifanout)
                #for  h_port1, h_port2 in combinations(multifanout[sp]['ports'],2):
                #     recursive_start_points(multifanout[sp]['graph'],all_match_pairs,traversed.copy(),h_port1, h_port2, multifanout[sp]['ports_weight'])   
            else:
                logger.debug(f"no symmetry from {sp}")
    except NameError:
        logger.debug("")
        

def FindSymmetry(graph, ports:list, ports_weight:dict, stop_points:list):
    """
    Find matching constraint starting from all port pairs.
    check: recursive_start_points
    Parameters
    ----------
    graph : graph
        DESCRIPTION.
    ports : list
        list of all subckt ports.
    ports_weight : dict
        used for matching port properties.
    stop_points : list
        starts with power, ground and clock signals adds based on traversal.

    Returns
    -------
    None.

    """
    #traversed =stop_points.copy()
    all_match_pairs={}
    for port1,port2 in combinations_with_replacement(set(sorted(ports))-set(stop_points),2):
        traversed =stop_points.copy()
        if sorted(ports_weight[port1]) == sorted(ports_weight[port2]) !=[0]:
            traversed+=[port1,port2]
            recursive_start_points(graph,all_match_pairs,traversed,port1,port2, ports_weight)
            logger.debug(f"all matches found starting from {port1} and {port2} pair: {all_match_pairs}")

    return all_match_pairs

def WriteConst(graph, input_dir, name, ports, ports_weight, all_array, stop_points=None):
    const_file = (input_dir / (name + '.const'))
    logger.debug("writing constraints: %s",const_file)
    logger.debug(f"ports weight: {ports_weight} stop_points : {stop_points}")


    # Read contents of input constraint file
    # Check if there are any other constraints except cap constraints
    # No constraints are written in case constraints are provided
    logger.info("input const file: %s", const_file)
    if const_file.exists() and const_file.is_file():
        with open(const_file) as f:
            for content in f:
                logger.info("line %s",content)
                if 'SymmBlock' in content or 'SymmNet' in content:
                    return
    all_match_pairs=FindSymmetry(graph.copy(), ports, ports_weight, stop_points)
                    
    written_symmetries = 'all'
    const_fp = open(const_file, 'a+')
    const_fp.write("// ALIGN generated automatic constraints")
    ## ALIGN block constraints
    align_const_keys =[key for key,value in all_match_pairs.items() if isinstance(value,list)]
    check_duplicate=[]
    for key in align_const_keys:
        array=all_match_pairs[key]
        logger.debug(f"group1: {array}")
        h_blocks=[ele for ele in array if ele in graph and ele not in check_duplicate]
        if len(h_blocks)>0:
            check_duplicate+=h_blocks
            h_align = "\nAlignBlock ( H , "+' , '.join(h_blocks)+' )'
            logger.debug("align constraint"+h_align)
            const_fp.write(h_align)
        del all_match_pairs[key]
    new_hier_keys =  [key for key,value in all_match_pairs.items() if "name" in value.keys()]
    for key in new_hier_keys:
        del all_match_pairs[key]
    
    for pairs in sorted(all_match_pairs.values(), key=lambda k: len (k.keys()), reverse=True):
        symmBlock='\nSymmBlock ('
        for key, value in pairs.items():
            #print("key,value,hier",key,value,new_hier_keys)
            if key in stop_points or key in written_symmetries or \
                value in written_symmetries or key in new_hier_keys or \
                key not in graph.nodes() or \
                graph.nodes[key]["inst_type"]!=graph.nodes[value]["inst_type"]:
                logger.debug(f"skipping symmetry b/w {key} {value}")
                continue
            if graph.nodes[key]["inst_type"]!="net" and \
                'Dcap' not in graph.nodes[key]["inst_type"] :
                if key !=value:
                    symmBlock += ' {'+key+ ','+value+'} ,'
                elif "Switch_" not in graph.nodes[key]["inst_type"]:
                    symmBlock +=' {' + key +'} ,'
                written_symmetries += symmBlock
            elif 'Dcap' not in graph.nodes[key]["inst_type"] :
                nbrs_key = [graph.get_edge_data(key, nbr)['weight'] for nbr in list(set(graph.neighbors(key)))]
                nbrs_val = [graph.get_edge_data(value, nbr)['weight'] for nbr in list(set(graph.neighbors(value)))]
                # second constraint was added due to ports coming as extra from connection function
                if nbrs_key != nbrs_val and connection(graph,key)!=connection(graph,value) :
                    logger.info(f"filtering nets which came due to S/D traversal {key} {value}{nbrs_key} {nbrs_val}")
                #elif key!=value  :
                    #pairs = symmnet_device_pairs(graph,connection(graph,key),connection(graph,value))
                    #symmNet = "\nSymmNet ( {"+key+','+','.join(pairs.keys()) + \
                    #        '} , {'+value+','+','.join(pairs.values()) +'} )'
                    #const_fp.write(symmNet)
                    #written_symmetries += ' '+ key+ ','+value + ','.join(pairs.keys()) + ','.join(pairs.values())
                else:
                    logger.debug(f"skip self symmetric nets")
        if ',' in symmBlock[:-1]:
            symmBlock = symmBlock[:-1]+')'
            written_symmetries.replace(key,'')
            const_fp.write(symmBlock)

    const_fp.close()

def symmnet_device_pairs(G, list_A, list_B):
    """
    

    Parameters
    ----------
    G : networkx graph
        subckt graphs.
    list_A/B : neighbors (device/pin) of net A/B
        DESCRIPTION.

    Returns
    -------
    pairs : dict
        deviceA/pin: deviceB/pin.
    """
    logger.info(f"arranging symmnet pairs {list_A} {list_B}")
    weight_A={}
    for ele  in list_A:
        node=ele.split('/')[0]
        weight_A[ele]=[]
        for nbr in list(G.neighbors(node)):
            weight_A[ele].append(G.get_edge_data(node, nbr)['weight'])            
    weight_B={}
    for ele  in list_B:
        node=ele.split('/')[0]
        weight_B[ele]=[]
        for nbr in list(G.neighbors(node)):
            weight_B[ele].append(G.get_edge_data(node, nbr)['weight'])
    pairs={}
    for ele_A in weight_A.keys():
        for ele_B in weight_B.keys():
            if weight_A[ele_A]==weight_B[ele_B] and ele_B not in pairs.values():
                pairs[ele_A]=ele_B
    return pairs
        

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
