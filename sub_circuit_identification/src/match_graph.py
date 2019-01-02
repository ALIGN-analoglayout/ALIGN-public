# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""
#%%
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import isomorphism
import numpy as np
import os,sys
import pickle
from merge_nodes import merge_nodes
from util import max_connectivity,plt_graph

#%%
def traverse_hier_in_graph(G,hier_graph_dict):
    for node,attr in G.nodes(data=True):
        if "sub_graph" in attr and not (attr["sub_graph"] == "NULL") :
            hier_graph_dict[attr["inst_type"]]={"graph":attr["sub_graph"],
                                               "ports":attr["ports"]
                                               }
            traverse_hier_in_graph(attr["sub_graph"],hier_graph_dict)            
            #plt_graph(attr["sub_graph"],attr["inst_type"])
                    
#%%
def read_inputs(file):
    hier_graph_dict={}
    hier_graph=nx.read_yaml(file)
    plt_graph(hier_graph,"Original_graph")
    top_ports=[]
    for node,attr in hier_graph.nodes(data=True):
        if 'source' in attr['inst_type']:
            for source_nets in hier_graph.neighbors(node):
                top_ports.append(source_nets)
    top_ports=list(set(top_ports))                       
    hier_graph_dict["top"]={"graph":hier_graph,
                           "ports":top_ports
                           }
    traverse_hier_in_graph(hier_graph,hier_graph_dict)
    return hier_graph_dict
#%%
def read_lib(lib_dir_path):
    library_dir_path= lib_dir_path
    lib_files = os.listdir(library_dir_path)
    if os.path.isfile("dont_use_cells.txt"):
        print("Reading Dont Use cells: dont_use_cells.txt")
        with open('dont_use_cells.txt') as f:
            dont_use_library = f.read().splitlines()
    else: print("no dont use list defined")

    library = []
    for sub_block_name in lib_files:
        graph = nx.read_yaml(library_dir_path+sub_block_name)
        if sub_block_name[:-5] not in dont_use_library:
            subgraph_ports=[]
            for node,attr in graph.nodes(data=True):
                if 'net' in attr['inst_type']:
                    if 'external' in attr['net_type']:
                        #print("external nets",node)
                        subgraph_ports.append(node)
            library.append ({"name":sub_block_name[:-5],"lib_graph":graph,"ports":subgraph_ports,"conn":max_connectivity(graph)})

    return sorted(library, key=lambda k: k['conn'],reverse=True)

#%%
#print(newlist)
def _mapped_graph_list(G1,newlist):
    mapped_graph_list={}

    for lib_ele in newlist:
        G2=lib_ele['lib_graph']
        sub_block_name=lib_ele['name']
        #print("Matching:",sub_block_name)
        #print("Matching:",sub_block_name,G2.nodes())
        #print("circuit node",G1.nodes())
        GM = isomorphism.GraphMatcher(G1,G2,node_match=isomorphism.categorical_node_match(['inst_type'],['nmos']),
                                      edge_match=isomorphism.categorical_multiedge_match(['weight'],[1]))
        if  GM.subgraph_is_isomorphic():
            #print("\n\nISOMORPHIC",sub_block_name)
            map_list=[]
            for Gsub in GM.subgraph_isomorphisms_iter():
                map_list.append(Gsub)
            mapped_graph_list[sub_block_name]=  map_list
            #print(mapped_graph_list[sub_block_name])
    
    return mapped_graph_list

def reduce_graph(G1,mapped_graph_list,liblist):
    newlist=liblist
    updated_circuit = []
    #print("all matches found")
    for lib_ele in newlist:
        G2=lib_ele['lib_graph']
        sub_block_name=lib_ele['name']
        sub_block_ports=lib_ele['ports']
        
        if  sub_block_name in mapped_graph_list:
            #print("\n\nISOMORPHIC",sub_block_name)
       
            for Gsub in mapped_graph_list[sub_block_name]:
    
                #print("matching nodes", Gsub)
                already_merged=0
                for g1_node in Gsub:
                    if g1_node not in  G1: already_merged=1
                if already_merged:
                     continue
                remove_these_nodes = [key for key in Gsub if 'net' not in G1.nodes[key]["inst_type"]]
                # Define ports for subblock
                matched_ports={}
                for g1_node in Gsub:
                    if 'net' not in G1.nodes[g1_node]["inst_type"]:continue
                    g2_node=Gsub[g1_node]
                    #print("G1:G2",g1_node,g2_node)
                    if 'external' in G2.nodes[g2_node]["net_type"]:
                        matched_ports[g2_node]=g1_node
                
                if len(remove_these_nodes)==1:
                    G1.nodes[remove_these_nodes[0]]["inst_type"]= sub_block_name
                    G1.nodes[remove_these_nodes[0]]["ports_match"]= matched_ports
                
                else:
                    reduced_graph,subgraph = merge_nodes(G1,sub_block_name,remove_these_nodes,matched_ports)
                    #plt_graph(reduced_graph,"reduced_graph")
                    plt_graph(subgraph,sub_block_name)
                    #print(sub_block_name)
                    updated_circuit.append ({"name":sub_block_name,"lib_graph":subgraph,"ports_match":matched_ports,"size":len(subgraph.nodes())})
                #print("found one subgraph")
    return updated_circuit,G1

if __name__ == '__main__':
    circuit_graph_dir = "circuit_graphs/"
    circuit_graph = os.listdir(circuit_graph_dir)
    if len(circuit_graph)>1:
        print("\nmore than one graphs in available in dir please run 'clean'")
        exit(0)
    circuit_graph=circuit_graph[0]
    input_circuit_file = circuit_graph_dir+circuit_graph
    library_dir_path= "library_graphs/"

    input_graph_dict=read_inputs(input_circuit_file)
    newlist=read_lib(library_dir_path)
    updated_circuit_list=[]
    for circuit_name, circuit in input_graph_dict.items():
        G1=circuit["graph"]
        mapped_graph_list=_mapped_graph_list(G1,newlist)
        #for key,value in mapped_graph_list.items():
        #    print("match",key)
        updated_circuit,Grest=reduce_graph(G1,mapped_graph_list,newlist)
     
        rest_nodes= [x for x,y in Grest.nodes(data=True) if 'mos' in y['inst_type']]
        #print('Remaining nodes', rest_nodes)
        # Create top ports by removing sources from top
        updated_circuit_list.extend(updated_circuit)


            
        updated_circuit_list.append ({"name":circuit_name,"lib_graph":Grest,"ports":circuit["ports"], "size":len(Grest.nodes())})
    plt_graph(Grest,"Final reduced graph") 

    #for element in reduced_circuit:
    #    print("\nName: nodes",element["name"],element["ports_match"],element["lib_graph"].nodes())
    if not os.path.exists("results"):
        os.mkdir("results")        
    with open('results/'+circuit_graph[:-5]+'.p', 'wb') as handle:
        pickle.dump(updated_circuit_list, handle, protocol=pickle.HIGHEST_PROTOCOL)
# %%
