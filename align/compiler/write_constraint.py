# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""

import pprint
from itertools import combinations,combinations_with_replacement
import logging
logger = logging.getLogger(__name__)

def find_unique_matching_branches(G,nbrs1,nbrs2,ports_weight):
    logger.debug(f"finding unique matches between {nbrs1},{nbrs2}")
    match={}
    for node1 in nbrs1:
        for node2 in nbrs2:
            if compare_two_nodes(G, node1, node2, ports_weight):
                if node1 in match:
                    return False
                else:
                    match[node1]=node2
        if node1 not in match:
            return False

    return match
        
    
def compare_two_nodes(G,node1:str,node2:str ,ports_weight):
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
    nbrs1= [nbr for nbr in G.neighbors(node1) if G.get_edge_data(node1, nbr)['weight'] !=2]
    nbrs2= [nbr for nbr in G.neighbors(node2) if G.get_edge_data(node2, nbr)['weight'] !=2]
    nbrs1= [nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['weight'] !=7]
    nbrs2= [nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)['weight'] !=7]
    logger.debug(f"comparing_nodes: {node1},{node2},{nbrs1},{nbrs2}")

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
            weight1=[(G.get_edge_data(node1, nbr)['weight'] & ~2) for nbr in nbrs1]
            weight2=[(G.get_edge_data(node2, nbr)['weight'] & ~2) for nbr in nbrs2]
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


def compare_nodes(G,all_match_pairs,match_pair,traversed,node1,node2, ports_weight):
    """
    Traversing single branch for symmetry
    condition 1, Single branch: both ports/ nets are same and connected to two or more ports
    condition 2, Converging branch: two nets are diffrent but connected to single device node
    condition 3: Two parallel branches
    condition 3: Two branches with multiple fanout will create new start points
    condition 4: Diverging branch with more than 2 fanout, check all pairs

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
    nbrs1 = sorted(set(G.neighbors(node1)) - set(traversed))
    nbrs1 = sorted(set([nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['weight'] !=7]))
    nbrs2 = sorted(set(G.neighbors(node2)) - set(traversed))
    nbrs2 = sorted(set([nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)['weight'] !=7]))
    logger.debug(f"first node1:{node1},property: {G.nodes[node1]},neigbors1: {nbrs1}")
    logger.debug(f"second node2:{node2},property: {G.nodes[node2]},neigbors2: {nbrs2}")
    if not nbrs1 or not nbrs2:
        if compare_two_nodes(G, node1, node2, ports_weight):
            match_pair[node1]=node2
        logger.debug(f"no new neihbours, returning recursion {match_pair}")
        return
    
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
            #match_pair[node1]=node1 
        elif len(SD_nbrs) ==1:
            logger.debug(f"traversing single S/D path ")
            match_pair[node1]=node1 
            traversed.append(node1)
            compare_nodes(G,all_match_pairs,match_pair,traversed,SD_nbrs[0],SD_nbrs[0],ports_weight)            
        else:        
            logger.debug(f" multiple nodes diverging {nbrs1} {SD_nbrs}")
            logger.debug(f"nbr weights: {SD_nbrs} {[G.get_edge_data(node1, nbr)['weight'] for nbr in SD_nbrs  ]}")
            match_pair[node1]=node1
            traversed.append(node1)
            new_sp=sorted(set(SD_nbrs)-set(traversed))
            all_match_pairs_local={}
            for nbr1,nbr2 in combinations(new_sp, 2):
                logger.debug(f"recursive pair call from single branch {nbr1} {nbr2}")
                new_pair={}
                compare_nodes(G,all_match_pairs,new_pair,traversed.copy(),nbr1,nbr2,ports_weight)
                if new_pair:
                    #new_pair[nbr1]=nbr2
                    all_match_pairs_local[nbr1+'_'+nbr2] = new_pair
            all_match_pairs_local={k: v for k, v in all_match_pairs_local.items() if len(v)>0}
            if len(all_match_pairs_local)==1:
                match_pair.update( all_match_pairs_local[list(all_match_pairs_local.keys())[0]])
                logger.debug(f"found inline pair: {pprint.pformat(match_pair, indent=4)}")
            else:
                for nbr1 in new_sp:
                    logger.debug(f"recursive single branch call from single branch {nbr1} {nbr1}")
                    new_pair={}
                    compare_nodes(G,all_match_pairs,new_pair,traversed.copy(),nbr1,nbr1,ports_weight)
                    if new_pair and nbr1+'_'+nbr1 in all_match_pairs.keys():
                        all_match_pairs[nbr1+'_'+nbr1].update(new_pair)
                        logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")
                    elif new_pair:
                        all_match_pairs[nbr1+'_'+nbr1] = new_pair
                        logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")


    elif nbrs1 == nbrs2:
        logger.debug(f"traversing converging branch")
        match_pair[node1]=node2
        traversed+=[node1,node2]
        nbrs1=sorted(set(nbrs1)-set([node1,node2]))
        logger.debug(f"all non traversed neighbours: {nbrs1}")
        if len(nbrs1)==1:
            nbr1=nbr2=nbrs1[0]
            logger.debug(f"keeping single converged branch inline {nbr1} {nbr2}")
            compare_nodes(G,all_match_pairs,match_pair,traversed.copy(),nbr1,nbr2,ports_weight)
        else:
            for nbr1,nbr2 in combinations_with_replacement(nbrs1,2):
                logger.debug(f"recursive call from converged branch {nbr1} {nbr2}")
                new_pair={}
                compare_nodes(G,all_match_pairs,new_pair,traversed.copy(),nbr1,nbr2,ports_weight)
                if new_pair and nbr1+'_'+nbr2 in all_match_pairs.keys():
                    all_match_pairs[nbr1+'_'+nbr2].update(new_pair)
                    logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")
                elif new_pair:
                    all_match_pairs[nbr1+'_'+nbr2] = new_pair
                    logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")
        

    elif compare_two_nodes(G,node1,node2,ports_weight):
        nbrs1 = sorted(set([nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)['weight'] !=2]))
        nbrs2 = sorted(set([nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)['weight'] !=2]))
        match_pair[node1]=node2
        traversed+=[node1,node2]
        logger.info(f"Traversing parallel branches from {node1},{node2} {nbrs1}, {nbrs2}")
        nbrs1_wt = [G.get_edge_data(node1, nbr)['weight'] for nbr in nbrs1]
        nbrs2_wt = [G.get_edge_data(node2, nbr)['weight'] for nbr in nbrs2]
        unique_match=find_unique_matching_branches(G,nbrs1,nbrs2,ports_weight)
        if  len(nbrs1)==0 or len(nbrs2)==0:
            logger.debug(f"no new SD neihbours, returning recursion {match_pair}")
        elif len(nbrs1) ==1 and len(nbrs2)==1:
            logger.debug(f"traversing binary branch")
            compare_nodes(G,all_match_pairs,match_pair,traversed,nbrs1.pop(),nbrs2.pop(),ports_weight)
        elif unique_match:
            logger.debug(f'traversing unique matches {unique_match}')
            match_pair[node1]=node2
            traversed+=[node1,node2]
            for nbr1,nbr2 in unique_match.items():
                logger.debug(f"recursive call from binary {node1}:{node2} to {nbr1}:{nbr2}")
                compare_nodes(G,all_match_pairs,match_pair,traversed.copy(),nbr1,nbr2,ports_weight)
        elif len(nbrs1_wt)>len(set(nbrs1_wt))>1 and len(nbrs2_wt)>len(set(nbrs2_wt))>1:
            logger.debug(f"setting new start points {node1} {node2}")
            match_pair[node1]=node2
            if "start_point" in match_pair.keys():
                match_pair["start_point"]+=[node1,node2]
            else:
                match_pair["start_point"]=[node1,node2]
        else:
            match_pair = {}
            logger.debug(f"end all traversal from binary branch {node1} {node2}")
        
    else:
        match_pair = {}
        logger.debug(f"end of recursion branch, matches {match_pair}")

def recursive_start_points(G,all_match_pairs,traversed,node1,node2, ports_weight):
    logger.debug(f"symmetry start point {node1} {node2}")
    pair ={}
    compare_nodes(G,all_match_pairs, pair, traversed, node1, node2,ports_weight)
    all_match_pairs[node1+node2]=pair                         
    logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")

    for k,pair in all_match_pairs.items():
        logger.debug(f"all pairs from {k}:{pair}")
        if "start_point" in pair.keys():
            hier_start_points=pair["start_point"]    
            del pair["start_point"]
            logger.debug(f"New symmetrical start points {pair}")
    all_match_pairs={k: v for k, v in all_match_pairs.items() if len(v)>0}
    logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")
    try: 
        for sp in sorted(hier_start_points):
            logger.debug(f"starting new node from binary branch:{sp} {hier_start_points} traversed {traversed}")
            if sp not in G.nodes():
                continue
            multifanout = create_hierarchy(G,sp,traversed,ports_weight)
            if  multifanout and isinstance(multifanout[sp], list):
                logger.debug(f"only one level matched so putting as align block:{multifanout[sp]}")
                all_match_pairs[node1+node2+'_align']=multifanout[sp]
            elif multifanout and isinstance(multifanout[sp], dict):
                logger.debug(f"more than one depth matched so creating new hierarchy :{multifanout[sp]}")
                traversed+=[node1,node2]
                all_match_pairs[sp+'_new_hier']=multifanout[sp]
                
                logger.debug("new hier list %s %s",sp, multifanout)
                #for  h_port1, h_port2 in combinations(multifanout[sp]['ports'],2):
                #     recursive_start_points(multifanout[sp]['graph'],all_match_pairs,traversed.copy(),h_port1, h_port2, multifanout[sp]['ports_weight'])   
            else:
                logger.debug(f"no symmetry from {sp}")
            logger.debug(f"updating match pairs: {pprint.pformat(all_match_pairs, indent=4)}")
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
    all_match_pairs={}
    non_power_ports=sorted(set(sorted(ports))-set(stop_points))
    logger.debug(f"sorted ports: {non_power_ports}")
    for port1,port2 in combinations_with_replacement(non_power_ports,2):
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
        return
        ## Designer want file based check
        with open(const_file) as f:
            for content in f:
                logger.info("line %s",content)
                if 'SymmBlock' in content or 'SymmNet' in content:
                    return
    all_match_pairs=FindSymmetry(graph.copy(), ports, ports_weight, stop_points)
    all_match_pairs={k: v for k, v in all_match_pairs.items() if len(v)>1}
    logger.debug(f"all symmetry matching pairs {pprint.pformat(all_match_pairs, indent=4)}")            
    written_symmetries = ''
    ## ALIGN block constraints
    const_all=[]
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
            const_all.write(h_align)
        del all_match_pairs[key]

    new_hier_keys =  [key for key,value in all_match_pairs.items() if "name" in value.keys()]
    for key in new_hier_keys:
        del all_match_pairs[key]
    
    all_pairs=sorted(all_match_pairs.values(), key=lambda k: len ([k1 for k1,v1 in k.items() if k1!=v1]), reverse=True)
    logger.debug(f"all symmtry matching pairs {pprint.pformat(all_pairs, indent=4)}")            
    for pairs in all_pairs:
        symmBlock='\nSymmBlock ('
        pairs=sorted(pairs.items(),key=lambda k: k[0])
        logger.debug(f"all symmblock pairs {pairs} {written_symmetries}")
        for key, value in pairs:
            #print("key,value,hier",key,value,new_hier_keys)
            if key in stop_points:
                logger.debug(f"skipping symmetry b/w {key} {value} as they are present in stop_points")
                continue
            elif key in written_symmetries or value in written_symmetries:
                logger.debug(f"skipping symmetry b/w {key} {value} as already written {written_symmetries}")
                continue
            elif key in new_hier_keys:
                logger.debug(f"skipping symmetry b/w {key} {value} as {key} is merged to another hierarchy")
                continue
            elif key not in graph.nodes():
                logger.debug(f"skipping symmetry b/w {key} {value} as {key} is not in graph")
                continue
            elif graph.nodes[key]["inst_type"]!=graph.nodes[value]["inst_type"]:
                logger.debug(f"skipping symmetry b/w {key} {value} due to instance type mismatch")
                continue
            if graph.nodes[key]["inst_type"]=="net" :
                if key!=value  :
                    pairs = symmnet_device_pairs(graph,key,value)
                    if pairs:
                        symmNet = "\nSymmNet ( {"+key+','+','.join(pairs.keys()) + \
                                '} , {'+value+','+','.join(pairs.values()) +'} )'
                        written_symmetries += symmNet
                        logger.debug(f"adding symmetries: {symmNet}")
                    else:
                        logger.debug("skipping symmetry between large fanout nets {key} {value}")
                        logger.debug("TBF:Need update in placer to simplify this")
                else:
                    logger.debug(f"skipping self symmetric nets {key} {value}")
            elif 'Dcap' in graph.nodes[key]["inst_type"]:
                logger.debug(f"skipping symmetry for dcaps {key} {value}") 
            else:
                if key !=value:
                    symmBlock += ' {'+key+ ','+value+'} ,'
                elif "Switch_" in graph.nodes[key]["inst_type"]:
                    logger.debug(f"TBF:skipping self symmetry for single transistor {key} {value}")
                else:
                    symmBlock +=' {' + key +'} ,'
        if ',' in symmBlock[:-1]:
            symmBlock = symmBlock[:-1]+')'
            written_symmetries += symmBlock
            logger.debug(f"one axis of written symmetries: {written_symmetries}")

    const_fp = open(const_file, 'a+')
    const_fp.write("// ALIGN generated automatic constraints")
    const_fp.write(written_symmetries)
    const_fp.close()

def symmnet_device_pairs(G, net_A, net_B):
    """
    Parameters
    ----------
    G : networkx graph
        subckt graphs.
    net_A/B : two nets A/B
        DESCRIPTION.

    Returns
    -------
    pairs : dict
        deviceA/pin: deviceB/pin.
    """
    conn_A = connection(G,net_A)
    conn_B = connection(G,net_B)

    pairs={}
    for ele_A in conn_A.keys():
        for ele_B in conn_B.keys():
            if conn_A[ele_A]==conn_B[ele_B] and G.nodes[ele_A.split('/')[0]]["inst_type"]==G.nodes[ele_B.split('/')[0]]["inst_type"]:
                if ele_B in pairs.values():
                    logger.debug(f"skipping symmetry due to multiple possible matching of net nbr {ele_B} to {pairs.values()} ")
                    pairs = {}
                    return pairs
                else:
                    pairs[ele_A]=ele_B
    return pairs
        

def connection(graph,net:str):
    """
    Returns all pins and ports connected to the net

    Parameters
    ----------
    graph : networkx graph
        subckt graphs.

    net : str
        name of net.

    Returns
    -------
    conn : list
        list of all pins and ports connected to a net.

    """
    conn = {}
    for nbr in list(graph.neighbors(net)):
        try:
            if "ports_match" in graph.nodes[nbr]:
                #logger.debug("ports match:%s %s",net,graph.nodes[nbr]["ports_match"].items())
                idx=list(graph.nodes[nbr]["ports_match"].values()).index(net)
                conn[nbr+'/'+list(graph.nodes[nbr]["ports_match"].keys())[idx]]= graph.get_edge_data(net, nbr)['weight']
                
            elif "connection" in graph.nodes[nbr]:
                #logger.debug("connection:%s%s",net,graph.nodes[nbr]["connection"].items())
                idx=list(graph.nodes[nbr]["connection"].values()).index(net)
                conn[nbr+'/'+list(graph.nodes[nbr]["connection"].keys())[idx]]= graph.get_edge_data(net, nbr)['weight']
        except ValueError:
            logger.debug("internal net")
    if graph.nodes[net]["net_type"]=="external":
        conn[net]=sum(conn.values())
    return conn

def CopyConstFile(name, input_dir, working_dir):
    """
    Copy const file to working directory if needed

    Parameters
    ----------
    name : str
        constraint filename.
    input_dir : path
    working_dir : path

    Returns
    -------
    const_file : path
        copied constraint file path.

    """
    input_const_file = (input_dir / (name + '.const'))
    const_file = (working_dir / (name + '.const'))
    if input_const_file.exists() and input_const_file.is_file():
        if const_file == input_const_file:
            (input_dir / (name + '.const.old')).write_text(input_const_file.read_text())
        else:
            const_file.write_text(input_const_file.read_text())
    return const_file
