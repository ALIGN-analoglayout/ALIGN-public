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

from merge_nodes import merge_nodes
from util import max_connectivity, plt_graph

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
logging.basicConfig(filename='./LOG/match.log', level=logging.DEBUG)


#%%
def traverse_hier_in_graph(G, hier_graph_dict):
    for node, attr in G.nodes(data=True):
        if "sub_graph" in attr and attr["sub_graph"]:
            logging.info("Traversing sub graph: %s", attr["inst_type"])
            sub_ports = []
            for sub_node, sub_attr in attr["sub_graph"].nodes(data=True):
                if 'net_type' in sub_attr:
                    if sub_attr['net_type'] == "external":
                        sub_ports.append(sub_node)

            hier_graph_dict[attr["inst_type"]] = {
                "graph": attr["sub_graph"],
                "ports": sub_ports
            }
            traverse_hier_in_graph(attr["sub_graph"], hier_graph_dict)
            #plt_graph(attr["sub_graph"],attr["inst_type"])


#%%
def read_inputs(file):
    hier_graph_dict = {}
    hier_graph = nx.read_yaml(file)
    plt_graph(hier_graph, "Original_graph")
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
    hier_graph_dict[file.split('/')[-1].split('.')[0]] = {
        "graph": hier_graph,
        "ports": top_ports
    }
    traverse_hier_in_graph(hier_graph, hier_graph_dict)
    return hier_graph_dict


#%%
def read_lib(lib_dir_path):
    library_dir_path = lib_dir_path
    lib_files = os.listdir(library_dir_path)
    if os.path.isfile("dont_use_cells.txt"):
        print("Reading Dont Use cells: dont_use_cells.txt")
        with open('dont_use_cells.txt') as f:
            dont_use_library = f.read().splitlines()
    else:
        print("no dont use list defined")

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
    logging.info("Matching circuit Graph from library elements")
    mapped_graph_list = {}

    for lib_ele in liblist:
        G2 = lib_ele['lib_graph']
        sub_block_name = lib_ele['name']
        #print("Matching:",sub_block_name)
        logging.info("Matching library element: %s : %s", sub_block_name,
                     str(' '.join(G2.nodes())))
        #GM = isomorphism.GraphMatcher(G1,G2,node_match=isomorphism.categorical_node_match(['inst_type'],['nmos']))
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
                logging.info("Matched Library nodes: %s",
                             str(' '.join(Gsub.values())))
                logging.info("Matched Circuit nodes: %s", str(' '.join(Gsub)))
            mapped_graph_list[sub_block_name] = map_list
            #print(mapped_graph_list[sub_block_name])

    return mapped_graph_list


def reduce_graph(G1, mapped_graph_list, liblist):
    logging.info("START reducing graph: ")
    updated_circuit = []
    #print("all matches found")
    for lib_ele in liblist:
        G2 = lib_ele['lib_graph']
        sub_block_name = lib_ele['name']
        sub_block_ports = lib_ele['ports']

        if sub_block_name in mapped_graph_list:
            logging.info("Reducing ISOMORPHIC sub_block: %s", sub_block_name)

            for Gsub in mapped_graph_list[sub_block_name]:
                already_merged = 0
                for g1_node in Gsub:
                    if g1_node not in G1:
                        already_merged = 1
                        logging.info("Skip merging. Node no more available: %s",
                                     g1_node)
                        break

                if already_merged:
                    continue
                remove_these_nodes = [
                    key for key in Gsub
                    if 'net' not in G1.nodes[key]["inst_type"]
                ]
                logging.info("Reducing nodes: %s", ', '.join(remove_these_nodes))

                # Define ports for subblock
                matched_ports = {}
                for g1_node, g2_node in Gsub.items():
                    if 'net' not in G1.nodes[g1_node]["inst_type"]:
                        G2.nodes[g2_node]['values'] = G1.nodes[g1_node][
                            'values']
                        continue
                    if 'external' in G2.nodes[g2_node]["net_type"]:
                        matched_ports[g2_node] = g1_node

                logging.info("Matched ports: %s", str(' '.join(matched_ports)))
                logging.info("Matched nets : %s",
                             str(' '.join(matched_ports.values())))

                if len(remove_these_nodes) == 1:
                    G1.nodes[
                        remove_these_nodes[0]]["inst_type"] = sub_block_name
                    G1.nodes[
                        remove_these_nodes[0]]["ports_match"] = matched_ports

                else:
                    reduced_graph, subgraph = merge_nodes(
                        G1, sub_block_name, remove_these_nodes, matched_ports)
                    #plt_graph(reduced_graph,"reduced_graph")
                    plt_graph(subgraph, sub_block_name)
                    logging.info('Calling recursive for bock: ' +
                                 sub_block_name)
                    mapped_subgraph_list = _mapped_graph_list(
                        G2, [
                            i for i in liblist
                            if not (i['name'] == sub_block_name)
                        ])
                    updated_subgraph_circuit, Grest = reduce_graph(
                        G2, mapped_subgraph_list, liblist)
                    updated_circuit.extend(updated_subgraph_circuit)
                    updated_circuit.append({
                        "name": sub_block_name,
                        "lib_graph": Grest,
                        "ports_match": matched_ports,
                        "size": len(subgraph.nodes())
                    })
                    #updated_circuit.append ({"name":sub_block_name,"lib_graph":subgraph,"ports_match":matched_ports,"size":len(subgraph.nodes())})
    return updated_circuit, G1


if __name__ == '__main__':
    CIRCUIT_GRAPH_DIR = "circuit_graphs/"
    CIRCUIT_GRAPH = os.listdir(CIRCUIT_GRAPH_DIR)
    if not CIRCUIT_GRAPH:
        print("no graphs found, please run 'python ./src/read_netlist.py '")
    elif len(CIRCUIT_GRAPH) > 1:
        print(
            "\nmore than one graphs in available in dir please use'rm ./circuit_graphs/*'"
        )
        exit(0)

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

        logging.info("no of nodes: %s", str(len(circuit["graph"].nodes())))
        mapped_graph_list = _mapped_graph_list(G1, LIB_LIST)
        updated_circuit, Grest = reduce_graph(G1, mapped_graph_list, LIB_LIST)

        #rest_nodes= [x for x,y in Grest.nodes(data=True) if 'mos' in y['inst_type']]
        #print('Reduced netlist elements in block:',circuit_name,' : ',  Grest.nodes())
        # Create top ports by removing sources from top
        UPDATED_CIRCUIT_LIST.extend(updated_circuit)

        #print(circuit["ports"])

        UPDATED_CIRCUIT_LIST.append({
            "name": circuit_name,
            "lib_graph": Grest,
            "ports": circuit["ports"],
            "size": len(Grest.nodes())
        })

    plt_graph(Grest, "Final reduced graph")

    #for element in reduced_circuit:
    #    print("\nName: nodes",element["name"],element["ports_match"],element["lib_graph"].nodes())
    if not os.path.exists("results"):
        os.mkdir("results")
    with open('results/' + CIRCUIT_GRAPH[:-5] + '.p', 'wb') as handle:
        pickle.dump(UPDATED_CIRCUIT_LIST,
                    handle,
                    protocol=pickle.HIGHEST_PROTOCOL)
# %%
