# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
import os
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import bipartite

#library_graphs = glob.glob("L1*.yaml")
def max_connectivity(G):
    conn_value =0 
    #internal_nets =[x for x,y in G.nodes(data=True) if y['inst_type']=='net' and len(G.edges(x)) > 1]
    for (u, v, wt) in G.edges.data('weight'):
        if G.nodes[u]['inst_type']=='net' and len(G.edges(u)) >1:
            if 'mos' in G.nodes[v]['inst_type'] and wt >3:
                conn_value-=2
            conn_value +=wt
            #print (u,conn_value)         
        elif G.nodes[v]['inst_type']=='net' and len(G.edges(v)) >1:
            if 'mos' in G.nodes[u]['inst_type'] and wt >3:
                conn_value-=2
            conn_value +=wt
            #print (v,conn_value)         
    return conn_value
def plt_graph(subgraph,sub_block_name):
    #print(sub_block_name,subgraph.nodes())
    #for x,y in subgraph.nodes(data=True):
    #    print(x,y)
    copy_graph=subgraph
    for node,attr in list(copy_graph.nodes(data=True)):
        #print(node)
        #print(copy_graph.nodes[node])
        if 'source' in attr["inst_type"]:
            #print("deleting source node",node)
            #   copy_graph.nodes(node)['inst_type']:
            copy_graph.remove_node(node)

    no_of_transistor =len([x for x,y in subgraph.nodes(data=True) if 'net' not in y['inst_type']] )
    Title=sub_block_name+", no of devices:"+ str(no_of_transistor)
    if no_of_transistor > 10 :
        plt.figure(figsize=(8, 6))
    else:
        plt.figure(figsize=(4, 3))
    nx.draw(copy_graph,with_labels=True,pos=nx.spring_layout(copy_graph))
    plt.title(Title, fontsize=20)
    #fig.savefig(Title+'.png', dpi=fig.dpi)
    
    #plt.show()
    #plt.show(block=False)
    #plt.pause(0.3) # pause how many seconds
    #plt.close()

def _show_circuit_graph(filename, graph, dir_path):
    #print(graph)
    no_of_subgraph = 0
    for subgraph in nx.connected_component_subgraphs(graph):
        no_of_subgraph += 1

        color_map = []

        plt.figure(figsize=(6, 8))
        for node, attr in subgraph.nodes(data=True):
            if "inst_type" in attr:
                if attr["inst_type"] == 'pmos':
                    color_map.append('red')
                elif attr["inst_type"] == 'nmos':
                    color_map.append('cyan')
                elif attr["inst_type"] == 'cap':
                    color_map.append('orange')
                elif attr["inst_type"] == 'net':
                    color_map.append('pink')
                else:
                    color_map.append('green')
        #%matplotlib inline
        nx.draw(subgraph, node_color=color_map)
        plt.title(filename, fontsize=20)
        if not os.path.exists(dir_path):
            os.mkdir(dir_path)
        plt.savefig(dir_path+'/'+ filename + "_" +
                    str(no_of_subgraph) + '.png')
        plt.close()
        #logging.info("Plot saved in graph images directory")

def _show_bipartite_circuit_graph(filename, graph, dir_path):
    #logging.info("Saving bipartite graph: %s", filename)
    #print(graph)
    no_of_subgraph = 0
    for subgraph in nx.connected_component_subgraphs(graph):
        no_of_subgraph += 1

        color_map = []
        x_pos, y_pos = bipartite.sets(subgraph)
        pos = dict()
        pos.update(
            (n, (1, i)) for i, n in enumerate(x_pos))  # put nodes from X at x=1
        pos.update(
            (n, (2, i)) for i, n in enumerate(y_pos))  # put nodes from Y at x=2
        #nx.draw(B, pos=pos)
        #plt.show()
        plt.figure(figsize=(6, 8))
        for dummy, attr in subgraph.nodes(data=True):
            if "inst_type" in attr:
                if attr["inst_type"] == 'pmos':
                    color_map.append('red')
                elif attr["inst_type"] == 'nmos':
                    color_map.append('cyan')
                elif attr["inst_type"] == 'cap':
                    color_map.append('orange')
                elif attr["inst_type"] == 'net':
                    color_map.append('pink')
                else:
                    color_map.append('green')
        nx.draw(subgraph, node_color=color_map, with_labels=True, pos=pos)
        plt.title(filename, fontsize=20)
        if not os.path.exists(dir_path):
            os.mkdir(dir_path)
        plt.savefig(dir_path+'/' + filename + "_" +
                    str(no_of_subgraph) + '.png')
        plt.close()
        #logging.info("Bipartite graph plot saved in graph images directory")


def _write_circuit_graph(filename, graph,dir_path):
    if not os.path.exists(dir_path):
        os.mkdir(dir_path)
    nx.write_yaml(graph, dir_path+'/' + filename + ".yaml")
    #logging.info("Graph saved in circuit_graphs directory")
    
def convert_to_unit(values):
    for param in values:
        if values[param]>= 1 :
            values[param]=int(values[param])                 
        elif values[param]*1E3> 1 :
            values[param]=str(int(values[param]*1E3))+'m'                                   
        elif values[param]*1E6>1 :
            values[param]=str(int(values[param]*1E6))+'u'               
        elif values[param]*1E9>1:
            values[param]=str(int(values[param]*1E9))+'n'
        elif values[param]*1E12>1:
            values[param]=str(int(values[param]*1E12))+'p'
        else:
            print("ERROR:WRONG value, %s",values)
            
            
