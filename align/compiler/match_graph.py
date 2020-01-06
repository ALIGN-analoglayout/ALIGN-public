# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""
#%%
import os
import logging
import pickle
import networkx as nx
from networkx.algorithms import isomorphism

from .merge_nodes import merge_nodes, merged_value,convert_unit
from .util import max_connectivity, logging


#%%
def traverse_hier_in_graph(G, hier_graph_dict):
    """
    Recusively reads all hierachies in the graph
    """
    for node, attr in G.nodes(data=True):
        if "sub_graph" in attr and attr["sub_graph"]:
            logging.info("Traversing sub graph:%s %s %s", node, attr["inst_type"],attr["ports"] )
            sub_ports = []
            for sub_node, sub_attr in attr["sub_graph"].nodes(data=True):
                if 'net_type' in sub_attr:
                    if sub_attr['net_type'] == "external":
                        sub_ports.append(sub_node)
             
            logging.info("external ports:%s,%s",sub_ports,attr["connection"])
            hier_graph_dict[attr["inst_type"]] = {
                "graph": attr["sub_graph"],
                "ports": sub_ports,
                "connection": attr["connection"]
            }
            traverse_hier_in_graph(attr["sub_graph"], hier_graph_dict)


#%%
def read_inputs(name,hier_graph):
    """
    read circuit graphs
    """
    hier_graph_dict = {}
    top_ports = []
    for node, attr in hier_graph.nodes(data=True):
        if 'source' in attr['inst_type']:
            for source_nets in hier_graph.neighbors(node):
                top_ports.append(source_nets)
        elif 'net_type' in attr:
            if attr['net_type'] == "external":
                top_ports.append(node)
    top_ports = list(set(top_ports))

    logging.info("READING top circuit graph: ")
    hier_graph_dict[name] = {
        "graph": hier_graph,
        "ports": top_ports,
        "connection": None
    }
    traverse_hier_in_graph(hier_graph, hier_graph_dict)
    return hier_graph_dict


#%%
def read_lib(lib_dir_path):
    """
    read all library graphs
    """
    library_dir_path = lib_dir_path
    lib_files = os.listdir(library_dir_path)
    if os.path.isfile("dont_use_cells.txt"):
        logging.info("Reading Dont Use cells: dont_use_cells.txt")
        with open('dont_use_cells.txt') as dont_use_file:
            dont_use_library = dont_use_file.read().splitlines()
    else:
        dont_use_library = []
        logging.info("no dont use list defined")

    library = []
    for sub_block_name in lib_files:
        graph = nx.read_yaml(library_dir_path + sub_block_name)
        if sub_block_name[:-5] not in dont_use_library:
            subgraph_ports = []
            for node, attr in graph.nodes(data=True):
                if 'net' in attr['inst_type']:
                    if 'external' in attr['net_type']:
                        subgraph_ports.append(node)
            library.append({
                "name": sub_block_name[:-5],
                "graph": graph,
                "ports": subgraph_ports,
                "conn": max_connectivity(graph)
            })
            logging.info("Read lib:%s%s",sub_block_name,subgraph_ports)

    return sorted(library, key=lambda k: k['conn'], reverse=True)


#%%
def _mapped_graph_list(G1, liblist, CLOCK=None, DIGITAL=False):
    """
    find all matches of library element in the graph
    """
    
    logging.info("Matching circuit Graph from library elements")
    mapped_graph_list = {}

    for lib_ele in liblist:
        G2 = lib_ele['graph']
        # DIgital blocks only transistors:
        nd = [node for node in G2.nodes()
                if 'net' not in G2.nodes[node]["inst_type"]]
        if DIGITAL and len(nd)>1:
            continue

        sub_block_name = lib_ele['name']
        #print("Matching:",sub_block_name)
        logging.info("Matching: %s : %s", sub_block_name,
                     str(' '.join(G2.nodes())))
        GM = isomorphism.GraphMatcher(
            G1, G2,
            node_match=isomorphism.categorical_node_match(['inst_type'],
                                                          ['nmos']),
            edge_match=isomorphism.categorical_edge_match(['weight'], [1]))

        if GM.subgraph_is_isomorphic():
            logging.info("ISOMORPHIC : %s", sub_block_name)
            map_list = []
            for Gsub in GM.subgraph_isomorphisms_iter():
                all_nd = [
                key for key in Gsub
                if 'net' not in G1.nodes[key]["inst_type"]]
                logging.info("matched inst: %s",all_nd)
                if len(all_nd)>1 and dont_touch_clk(Gsub,CLOCK):
                    logging.info("Discarding match due to clock")
                    continue
                if sub_block_name.startswith('DP') or sub_block_name.startswith('CMC'):
                    if G1.nodes[all_nd[0]]['values'] == G1.nodes[all_nd[1]]['values'] and \
                        compare_balanced_tree(G1,get_key(Gsub,'DA'),get_key(Gsub,'DB')) :
                        if 'SA' in Gsub.values() and \
                        compare_balanced_tree(G1,get_key(Gsub,'SA'),get_key(Gsub,'SB')) :
                            map_list.append(Gsub)
                            logging.info("Matched Lib: %s",str(' '.join(Gsub.values())))
                            logging.info("Matched Circuit: %s", str(' '.join(Gsub)))
                        else:
                            map_list.append(Gsub)
                            logging.info("Matched Lib: %s",str(' '.join(Gsub.values())))
                            logging.info("Matched Circuit: %s", str(' '.join(Gsub)))
                    else:
                        logging.info("Discarding match %s,%s,%s",sub_block_name,G1.nodes[all_nd[0]]['values'],G1.nodes[all_nd[1]]['values'])

                else:
                    map_list.append(Gsub)
                    logging.info("Matched Lib: %s",str(' '.join(Gsub.values())))
                    logging.info("Matched Circuit: %s", str(' '.join(Gsub)))
            mapped_graph_list[sub_block_name] = map_list

    return mapped_graph_list
#%%
def dont_touch_clk(Gsub,CLOCK):
    if CLOCK:
        for clk in CLOCK:
            if clk in Gsub:
                return True
    return False
def read_setup(setup_path):
    design_setup = {
            "POWER":['vdd'],
            "GND":[],
            "CLOCK":[],
            "DIGITAL":[],
            "DONT_USE_CELLS":[]
            }
    if os.path.isfile(setup_path):
        print('Reading setup file:', setup_path)
        fp = open(setup_path, "r")
        line = fp.readline()
        while line:
            if line.strip().startswith("POWER"):
                power = line.strip().split('=')[1].split()
                design_setup['POWER']=power
            elif line.strip().startswith("GND"):
                GND = line.strip().split('=')[1].split()
                design_setup['GND']=GND
            elif line.strip().startswith("CLOCK"):
                CLOCK = line.strip().split('=')[1].split()
                design_setup['CLOCK']=CLOCK
            elif line.strip().startswith("DIGITAL"):
                DIGITAL = line.strip().split('=')[1].split()
                design_setup['DIGITAL']=DIGITAL
            elif line.strip().startswith("DONT_USE_CELLS"):
                DONT_USE_CELLS = line.strip().split('=')[1].split()
                design_setup['DONT_USE_CELLS']=DONT_USE_CELLS
            else:
                print("Non identified values found",line)
            line=fp.readline()
        logging.info("SETUP:%s",design_setup)
    else:
        print("no setup file found:",setup_path)
    return design_setup
            
def get_key(Gsub, value):
    return list(Gsub.keys())[list(Gsub.values()).index(value)]

def get_next_level(G, tree_l1):
    tree_next=[]
    for node in list(tree_l1):
        if 'mos' in G.nodes[node]["inst_type"]:
            for nbr in list(G.neighbors(node)):
                if G.get_edge_data(node, nbr)['weight']!=2:
                    tree_next.append(nbr)
        elif 'net' in G.nodes[node]["inst_type"]:
            for nbr in list(G.neighbors(node)):
                if 'mos' in G.nodes[nbr]["inst_type"] and \
                 G.get_edge_data(node, nbr)['weight']!=2: 
                    tree_next.append(nbr)
        else:
            tree_next=list(G.neighbors(node))
    return tree_next


#%% 
def compare_balanced_tree(G, node1, node2):
    """
    used to remove some false matches for DP and CMC
    """
    logging.info("checking symmtrical connections for nodes: %s, %s",node1, node2)
    tree1 = set(get_next_level(G,[node1]))
    tree2 = set(get_next_level(G,[node2]))
    #logging.info("tree1 %s tree2 %s",set(tree1),set(tree2))
    traversed1 = [] 
    traversed2 = [] 
    if tree1==tree2:
        logging.info("common net or device")
        return True
    while(len(list(tree1))== len(list(tree2))):
        logging.info("tree1 %s tree2 %s",list(tree1),list(tree2))
        tree1 = set(tree1) ^ set(traversed1)
        tree2 = set(tree2) ^ set(traversed2)
        logging.info("removing traversed tree1 %s tree2 %s",set(tree1),set(tree2))
        #type1 = [G.nodes[node]["inst_type"] for node in list(tree1)]
        #type2 = [G.nodes[node]["inst_type"] for node in list(tree2)]
        if tree1.intersection(tree2):
            logging.info("matched subgraph")
            return True
        else:
            traversed1+=list(tree1)
            traversed2+=list(tree2)
            logging.info("traversing:tree1 %s tree2: %s",tree1,tree2)
            tree1=get_next_level(G,tree1)
            tree2=get_next_level(G,tree2)

    logging.warning("Non symmetrical branches for nets: %s, %s",node1, node2)
    return False

#%%
def reduce_graph(circuit_graph, mapped_graph_list, liblist):
    """
    merge matched graphs
    """
    logging.info("START reducing graph: ")
    G1 =circuit_graph.copy()
    updated_circuit = []
    for lib_ele in liblist:
        G2 = lib_ele['graph']
        sub_block_name = lib_ele['name']

        if sub_block_name in mapped_graph_list:
            logging.info("Reducing ISOMORPHIC sub_block: %s", sub_block_name)
            
            for Gsub in mapped_graph_list[sub_block_name]:
                already_merged = 0
                for g1_node in Gsub:
                    if g1_node not in G1:
                        already_merged = 1
                        logging.info("Skip merging. Node absent: %s",g1_node)
                        break

                if already_merged:
                    continue
                remove_these_nodes = [
                    key for key in Gsub
                    if 'net' not in G1.nodes[key]["inst_type"]]
                logging.info("Reduce nodes: %s",', '.join(remove_these_nodes))

                # Define ports for subblock
                matched_ports = {}
                for g1_n, g2_n in Gsub.items():
                    if 'net' not in G1.nodes[g1_n]["inst_type"]:
                        G2.nodes[g2_n]['values'] = G1.nodes[g1_n]['values']
                        #if 'mos' in G1.nodes[g1_n]["inst_type"] or \
                        find_body = G1.nodes[g1_n]['real_inst_type'].split('_')
                        if 'MOS' in sub_block_name and len(find_body) > 1:
                            #G1.nodes[g1_n]['real_inst_type']=find_body[0]
                            # Add body pin
                            matched_ports['B'] = find_body[-1]
                            logging.info('Adding body pin:%s %s',find_body,len(find_body))
                        #check_values(G2.nodes[g2_node]['values'])
                        continue
                    if 'external' in G2.nodes[g2_n]["net_type"]:
                        matched_ports[g2_n] = g1_n
                logging.info("match: %s",str(' '.join(Gsub)))
                logging.info("Matched ports: %s", str(' '.join(matched_ports)))
                logging.info("Matched nets : %s",
                             str(' '.join(matched_ports.values())))

                if len(remove_these_nodes) == 1:
                    logging.info("One node element: %s",sub_block_name)
                    G1.nodes[
                        remove_these_nodes[0]]["inst_type"] = sub_block_name
                    G1.nodes[
                        remove_these_nodes[0]]["ports_match"] = matched_ports
                    updated_values = merged_value({}, G1.nodes[remove_these_nodes[0]]["values"])
                    check_values(updated_values)
                    G1.nodes[remove_these_nodes[0]]["values"] = updated_values
                    for local_value in updated_values.values():
                        if not isinstance(local_value, float):
                            logging.error("unidentified sizing: %s", G1.nodes[remove_these_nodes[0]])

                else:
                    logging.info("Multi node element: %s",sub_block_name)

                    reduced_graph, subgraph = merge_nodes(
                        G1, sub_block_name, remove_these_nodes, matched_ports)
                    logging.info('Calling recursive for bock: %s',
                                 sub_block_name)
                    #print(sub_block_name)
                    #print(matched_ports)
                    mapped_subgraph_list = _mapped_graph_list(
                        G2, [
                            i for i in liblist
                            if not (i['name'] == sub_block_name)
                        ])
                    logging.info("Recursive calling to find sub_sub_ckt")
                    updated_subgraph_circuit, Grest = reduce_graph(
                        G2, mapped_subgraph_list, liblist)
                    check_nodes(updated_subgraph_circuit)

                    updated_circuit.extend(updated_subgraph_circuit)
                    logging.info("adding new sub_ckt: %s",sub_block_name)
                    check_nodes(updated_circuit)
                    logging.info("adding remaining ckt: %s",sub_block_name)
                    
                    updated_circuit.append({
                        "name": sub_block_name,
                        "graph": Grest,
                        "ports": list(matched_ports.keys()),
                        "ports_match": matched_ports,
                        "size": len(subgraph.nodes())
                    })
                    check_nodes(updated_circuit)
    logging.info("Finished one branch:%s", sub_block_name)

    return updated_circuit, G1
def change_SD(G,node):
    nbr = list(G.neighbors(node))
    #No gate change
    nbr = [nr for nr in nbr if G.get_edge_data(node, nr)['weight']!=2]
    #Swapping D and S
    w1 = G.get_edge_data(node, nbr[0])['weight']
    w2 = G.get_edge_data(node, nbr[1])['weight']
    G.get_edge_data(node, nbr[0])['weight'] = w2
    G.get_edge_data(node, nbr[1])['weight'] = w1

def define_SD(G,power,gnd,clk):
    logging.info("START checking source and drain in graph: ")
    try:
        gotpower=power[0]
        gotgnd=gnd[0]
        logging.info("using power: %s and ground: %s",gotpower,gotgnd)

    except (IndexError, ValueError):
        logging.error("no power and gnd defination, correct setup file")
        return False

    traversed = []
    probable_changes_p=[]
    if power[0] in G.nodes():
        while power:
            try:
                nxt = power[0]
                power = power[1:]
                high=get_next_level(G,[nxt]) 
                #logging.info("next,power: %s %s %s %s",nxt,power,high,traversed)
                for node in high:
                    if G.get_edge_data(node,nxt)==2:
                        continue
                    if set(G.neighbors(node)) & set(clk):
                        continue
                    #logging.info("checking node: %s %s", node, power)
                    if 'pmos' == G.nodes[node]["inst_type"] and \
                        node not in traversed: 
                        weight =G.get_edge_data(node, nxt)['weight']
                        if weight == 1 or weight==3 :
                            #logging.info("changing source drain:%s",node)
                            probable_changes_p.append(node)
                    elif 'nmos' == G.nodes[node]["inst_type"] and \
                    node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight']
                        if weight == 4 or weight==6 :
                            #logging.info("changing source drain:%s",node)
                            probable_changes_p.append(node)
                    if node not in traversed and node not in  gnd:
                        power.append(node)
                    traversed.append(node)
            except (TypeError, ValueError):
                logging.info("All source drain checked:%s",power)
    probable_changes_n=[]
    if gnd[0] in G.nodes():
        while gnd:
            try:
                nxt = gnd[0]
                gnd = gnd[1:]
                high=get_next_level(G,[nxt]) 
                logging.info("next,gnd: %s %s %s %s",nxt,gnd,high,traversed)
                for node in high:
                    if G.get_edge_data(node,nxt)==2:
                        continue
                    if set(G.neighbors(node)) & set(clk):
                        continue
                    #logging.info("checking node: %s %s", node, gnd)
                    if 'pmos' == G.nodes[node]["inst_type"] and \
                        node not in traversed: 
                        weight =G.get_edge_data(node, nxt)['weight']
                        if weight == 4 or weight==6 :
                            #logging.info("changing source drain:%s",node)
                            #change_SD(G,node)
                            probable_changes_n.append(node)
                    elif 'nmos' == G.nodes[node]["inst_type"] and \
                    node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight']
                        if weight == 1 or weight==3 :
                            #logging.info("changing source drain:%s",node)
                            #change_SD(G,node)
                            probable_changes_n.append(node)
                    if node not in traversed and node not in  power:
                        gnd.append(node)
                    traversed.append(node)
            except (TypeError, ValueError):
                logging.info("All source drain checked:%s",gnd)
    for node in list (set(probable_changes_n) & set(probable_changes_n)):
        logging.warning("changing source drain:%s",node)
        change_SD(G,node)


def add_parallel_caps(G):
    logging.info("merging all caps, initial graph size:%s", len(G))
    remove_nodes = []
    for node, attr in G.nodes(data=True):
        if 'cap' in attr["inst_type"] and node not in remove_nodes:
            for net in G.neighbors(node):
                for next_node in G.neighbors(net):
                    if not next_node == node  and next_node not in remove_nodes and G.nodes[next_node][
                        "inst_type"] == G.nodes[node]["inst_type"] and\
                        len(set(G.neighbors(node)) & set(G.neighbors(next_node)))==2:
                        for param, value in G.nodes[node]["values"].items():
                            if param == 'cap':
                                c_val = float(convert_unit(value))+ \
                                float(convert_unit(G.nodes[next_node]["values"]['cap']))
                                remove_nodes.append(next_node)
                                G.nodes[node]["values"]['cap']=c_val
                            elif param == 'c':
                                c_val = float(convert_unit(value))+ \
                                float(convert_unit(G.nodes[next_node]["values"]['c']))
                                remove_nodes.append(next_node)
                                G.nodes[node]["values"]['c']=c_val
    logging.info("removed parallel caps: %s",remove_nodes)
    for node in remove_nodes:
        G.remove_node(node)
def add_series_res(G):
    logging.info("merging all series res, initial graph size:%s", len(G))
    remove_nodes = []
    for net, attr in G.nodes(data=True):
        if 'net' in attr["inst_type"] and len(set(G.neighbors(net)))==2 \
            and net not in remove_nodes:
            nbr_type =[G.nodes[nbr]["inst_type"] for nbr in list(G.neighbors(net))]
            combined_r,remove_r=list(G.neighbors(net))
            if nbr_type[0]==nbr_type[1]=='res':
                remove_nodes.append(net)
                remove_nodes.append(remove_r)
                new_net=list(set(G.neighbors(remove_r))-set(net)-set(remove_nodes))[0]
                for param, value in G.nodes[combined_r]["values"].items():
                    if param == 'res':
                        r_val = float(convert_unit(value))+ \
                        float(convert_unit(G.nodes[remove_r]["values"]['res']))
                        G.nodes[combined_r]["values"]['res']=r_val
                        G.add_edge(combined_r, new_net, weight=G[combined_r][net]["weight"])
                    elif param == 'r':
                        r_val = float(convert_unit(value))+ \
                        float(convert_unit(G.nodes[remove_r]["values"]['r']))
                        G.nodes[combined_r]["values"]['r']=r_val
                        G.add_edge(combined_r, new_net, weight=G[combined_r][net]["weight"])
    logging.info("removed series r: %s",remove_nodes)
    for node in remove_nodes:
        G.remove_node(node)

def preprocess_stack(G):
    logging.info("START reducing  stacks in graph: ")
    logging.debug("initial size of graph:%s", len(G))
    #print("all matches found")
    remove_nodes = []
    modified_edges = {}
    modified_nodes = {}
    for node, attr in G.nodes(data=True):
        if 'mos' in attr["inst_type"] and node not in remove_nodes:
            for net in G.neighbors(node):
                edge_wt = G.get_edge_data(node, net)['weight']
                #print(" checking node: %s , %s",node,edge_wt)
                #print("neighbours:",list(G.neighbors(net)))
                if edge_wt == 4 and len(list(G.neighbors(net))) == 2:
                    for next_node in G.neighbors(net):
                        logging.info(" checking nodes: %s , %s",node,next_node)
                        if not next_node == node and G.nodes[next_node][
                                "inst_type"] == G.nodes[node][
                                    "inst_type"] and G.get_edge_data(
                                        next_node, net)['weight'] == 1:
                            common_nets = set(G.neighbors(node)) & set(
                                G.neighbors(next_node))
                            logging.info("stacking two transistors: %s , %s,%s",node,next_node,common_nets)
                            source_net = list(
                                set(G.neighbors(next_node)) - common_nets)[0]
                            if len(common_nets) == 2 and G.nodes[net]["net_type"]!="external":
                                #source_net = source_net[0]
                                common_nets.remove(net)
                                gate_net = list(common_nets)[0]
                                if G.get_edge_data(
                                        node, gate_net)['weight'] >= 2 and \
                                        G.get_edge_data(next_node, gate_net)\
                                        ['weight'] >= 2:

                                    lequivalent = 0
                                    for param, value in G.nodes[next_node][
                                            "values"].items():
                                        if param == 'l':
                                            #print("param1",node,param,value)
                                            lequivalent = float(
                                                convert_unit(value))
                                            logging.info("converted unit of 1st: %s",node)
                                    for param, value in G.nodes[node][
                                            "values"].items():
                                        if param == 'l':
                                            lequivalent += float(
                                                convert_unit(value))
                                            modified_nodes[node] = str(
                                                lequivalent)
                                            logging.info("converted unit of incr: %s",node)
                                    remove_nodes.append(net)
                                    modified_edges[node] = [
                                        source_net,
                                        G[next_node][source_net]["weight"]
                                    ]
                                    logging.info("success")
                                    remove_nodes.append(next_node)
    for node, attr in modified_edges.items():
        G.add_edge(node, attr[0], weight=attr[1])

    for node, attr in modified_nodes.items():
        G.nodes[node]["values"]['l'] = attr

    for node in remove_nodes:
        G.remove_node(node)

    logging.debug("reduced_size after resolving stacked transistor:%s", len(G))
    logging.debug(
        "\n######################START CREATING HIERARCHY##########################\n"
    )

def check_values(values):
    for param,value in values.items():
        logging.debug("param,value:%s,%s", param,value)
        if param == 'model': continue
        try:
            assert(isinstance(value, int) or isinstance(value, float))
        except AssertionError:
            print("ERROR: Parameter value",value, "not defined. Check match log")
            exit()
            
def check_nodes(graph_list):
    logging.debug("Checking all values")
    for local_subckt in graph_list:
        for node, attr in local_subckt["graph"].nodes(data=True):
            logging.debug(":%s,%s", node,attr)
            if  not attr["inst_type"] == "net":
                check_values(attr["values"])
