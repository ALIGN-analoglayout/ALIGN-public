# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
import networkx as nx
import matplotlib.pyplot as plt
#library_graphs = glob.glob("L1*.yaml")
def max_connectivity(G):
    conn_value =0 
    #internal_nets =[x for x,y in G.nodes(data=True) if y['inst_type']=='net' and len(G.edges(x)) > 1]
    for (u, v, wt) in G.edges.data('weight'):
        if G.nodes[u]['inst_type']=='net' and len(G.edges(u)) >1:
            conn_value +=wt
            #print (u,conn_value)         
        elif G.nodes[v]['inst_type']=='net' and len(G.edges(v)) >1:
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
        #print(copy_graph.node[node])
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

    plt.show(block=False)
    plt.pause(0.3) # pause how many seconds
    plt.close()
    
