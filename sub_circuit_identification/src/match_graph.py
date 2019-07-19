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

from merge_nodes import merge_nodes, merged_value,convert_unit
from util import max_connectivity

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
elif os.path.exists("./LOG/match.log"):
    os.rename("./LOG/match.log", "./LOG/match.log1")
logging.basicConfig(filename='./LOG/match.log', level=logging.DEBUG)


#%%
def traverse_hier_in_graph(G, hier_graph_dict):
    """
    Recusively reads all hierachies in the graph
    """
    for node, attr in G.nodes(data=True):
        if "sub_graph" in attr and attr["sub_graph"]:
            logging.info("Traversing sub graph:%s %s", node, attr["inst_type"])
            sub_ports = []
            for sub_node, sub_attr in attr["sub_graph"].nodes(data=True):
                if 'net_type' in sub_attr:
                    if sub_attr['net_type'] == "external":
                        sub_ports.append(sub_node)

            hier_graph_dict[attr["inst_type"]] = {
                "graph": attr["sub_graph"],
                "ports": sub_ports,
                "connection": attr["connection"]
            }
            traverse_hier_in_graph(attr["sub_graph"], hier_graph_dict)


#%%
def read_inputs(file_name):
    """
    read circuit graphs
    """
    hier_graph_dict = {}
    hier_graph = nx.read_yaml(file_name)
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
    hier_graph_dict[file_name.split('/')[-1].split('.')[0]] = {
        "graph": hier_graph,
        "ports": top_ports
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
                        #print("external nets",node)
                        subgraph_ports.append(node)
            library.append({
                "name": sub_block_name[:-5],
                "lib_graph": graph,
                "ports": subgraph_ports,
                "conn": max_connectivity(graph)
            })

    return sorted(library, key=lambda k: k['conn'], reverse=True)


#%%
def _mapped_graph_list(G1, liblist):
    """
    find all matches of library element in the graph
    """
    
    logging.info("Matching circuit Graph from library elements")
    mapped_graph_list = {}

    for lib_ele in liblist:
        G2 = lib_ele['lib_graph']
        sub_block_name = lib_ele['name']
        #print("Matching:",sub_block_name)
        logging.info("G: %s : %s", sub_block_name,
                     str(' '.join(G2.nodes())))
        GM = isomorphism.GraphMatcher(
            G1,
            G2,
            node_match=isomorphism.categorical_node_match(['inst_type'],
                                                          ['nmos']),
            edge_match=isomorphism.categorical_edge_match(['weight'], [1]))
        if GM.subgraph_is_isomorphic():
            logging.info("ISOMORPHIC : %s", sub_block_name)
            map_list = []
            for Gsub in GM.subgraph_isomorphisms_iter():
                map_list.append(Gsub)
                logging.info("Matched Lib: %s",str(' '.join(Gsub.values())))
                logging.info("Matched Circuit: %s", str(' '.join(Gsub)))
            mapped_graph_list[sub_block_name] = map_list

    return mapped_graph_list

#%%
def reduce_graph(circuit_graph, mapped_graph_list, liblist):
    """
    merge matched graphs
    """
    logging.info("START reducing graph: ")
    G1 =circuit_graph.copy()
    updated_circuit = []
    for lib_ele in liblist:
        G2 = lib_ele['lib_graph']
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
                        if not isinstance(local_value, int):
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
                        "lib_graph": Grest,
                        "ports_match": matched_ports,
                        "size": len(subgraph.nodes())
                    })
                    check_nodes(updated_circuit)
    logging.info("Finished one branch:%s", sub_block_name)

    return updated_circuit, G1


def preprocess_stack(G):
    logging.info("START reducing  stacks in graph: ")
    logging.debug("initial size of graph:%s", len(G))
    #print("all matches found")
    remove_nodes = []
    modified_edges = {}
    modified_nodes = {}
    for node, attr in G.nodes(data=True):
        if 'mos' in attr["inst_type"]:
            for net in G.neighbors(node):
                edge_wt = G.get_edge_data(node, net)['weight']
                #print(" checking node: %s , %s",node,edge_wt)
                #print("neighbours:",list(G.neighbors(net)))
                if edge_wt == 4 and len(list(G.neighbors(net))) == 2:
                    for next_node in G.neighbors(net):
                        logging.info(" checking nodes: %s , %s",node,next_node)
                        if not next_node == node and G.node[next_node][
                                "inst_type"] == G.node[node][
                                    "inst_type"] and G.get_edge_data(
                                        next_node, net)['weight'] == 1:
                            common_nets = set(G.neighbors(node)) & set(
                                G.neighbors(next_node))
                            logging.info("stacking two transistors: %s , %s,%s",node,next_node,common_nets)
                            source_net = list(
                                set(G.neighbors(next_node)) - common_nets)[0]
                            if len(common_nets) == 2:
                                #source_net = source_net[0]
                                common_nets.remove(net)
                                gate_net = list(common_nets)[0]
                                if G.get_edge_data(
                                        node, gate_net)['weight'] >= 2 and \
                                        G.get_edge_data(next_node, gate_net)\
                                        ['weight'] >= 2:

                                    lequivalent = 0
                                    for param, value in G.node[next_node][
                                            "values"].items():
                                        if param == 'l':
                                            #print("param1",node,param,value)
                                            lequivalent = float(
                                                convert_unit(value))
                                    for param, value in G.node[node][
                                            "values"].items():
                                        if param == 'l':
                                            lequivalent += float(
                                                convert_unit(value))
                                            modified_nodes[node] = str(
                                                lequivalent)
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
        G.node[node]["values"]['l'] = attr

    for node in remove_nodes:
        G.remove_node(node)

    logging.debug("reduced_size after resolving stacked transistor:%s", len(G))
    logging.debug(
        "\n######################START CREATING HIERARCHY##########################\n"
    )

def check_values(values):
    for param,value in values.items():
        logging.debug("param,value:%s,%s", param,value)
        try:
            assert(isinstance(value, int) or isinstance(value, float))
        except AssertionError:
            print("ERROR: Parameter value",value, "not defined. Check match log")
            exit()
            
def check_nodes(graph_list):
    logging.debug("Checking all values")
    for local_subckt in graph_list:
        for node, attr in local_subckt["lib_graph"].nodes(data=True):
            logging.debug(":%s,%s", node,attr)
            if  not attr["inst_type"] == "net":
                check_values(attr["values"])                 
    
        
    
if __name__ == '__main__':
    CIRCUIT_GRAPH_DIR = "circuit_graphs/"
    CIRCUIT_GRAPH = os.listdir(CIRCUIT_GRAPH_DIR)
    if not CIRCUIT_GRAPH:
        print("no graphs found, please run 'python ./src/read_netlist.py '")
    elif len(CIRCUIT_GRAPH) > 1:
        print("\nmultiple graphs in dir please use'rm ./circuit_graphs/*'")
        exit(0)
    print("Start matching graphs")
    CIRCUIT_GRAPH = CIRCUIT_GRAPH[0]
    INPUT_CKT_FILE = CIRCUIT_GRAPH_DIR + CIRCUIT_GRAPH
    logging.info("READING input circuit graph: %s", INPUT_CKT_FILE)
    INPUT_GRAPH_DICT = read_inputs(INPUT_CKT_FILE)
    logging.info("READING successful")

    LIBRARY_DIR_PATH = "library_graphs/"
    logging.info("READING input library graph: %s", LIBRARY_DIR_PATH)
    LIB_LIST = read_lib(LIBRARY_DIR_PATH)
    logging.info("READING successful")

    UPDATED_CIRCUIT_LIST = []
    for circuit_name, circuit in INPUT_GRAPH_DICT.items():
        logging.info("START MATCHING in circuit: %s", circuit_name)
        G1 = circuit["graph"]

        logging.info("no of nodes: %i", len(G1))
        #preprocess_stack(G1)
        initial_size=len(G1)
        delta =1
        while delta > 0:
            logging.info("CHECKING stacked transistors")
            preprocess_stack(G1)
            delta = initial_size - len(G1)
            initial_size = len(G1)


        mapped_graph_list = _mapped_graph_list(G1, LIB_LIST)
        updated_circuit, Grest = reduce_graph(G1, mapped_graph_list, LIB_LIST)

        # Create top ports by removing sources from top
        check_nodes(updated_circuit)
        UPDATED_CIRCUIT_LIST.extend(updated_circuit)

        UPDATED_CIRCUIT_LIST.append({
            "name": circuit_name,
            "lib_graph": Grest,
            "ports": circuit["ports"],
            "size": len(Grest.nodes())
        })

    #plt_graph(Grest, "Final reduced graph")

    if not os.path.exists("Results"):
        os.mkdir("Results")
    with open('Results/' + CIRCUIT_GRAPH[:-5] + '.p', 'wb') as handle:
        pickle.dump(UPDATED_CIRCUIT_LIST,
                    handle,
                    protocol=pickle.HIGHEST_PROTOCOL)
        
# %%
