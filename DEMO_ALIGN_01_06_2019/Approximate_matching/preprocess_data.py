# -*- coding: utf-8 -*-
"""
Created on Fri Dec  7 13:19:45 2018

@author: kunal
"""

import networkx as nx
import matplotlib.pyplot as plt
import numpy as np
import os,sys
import pickle
#from networkx import to_numpy_matrix
import pandas as pd
import csv

#%%
def laplacian_matrix( graph):
    L = nx.laplacian_matrix(graph, nodelist=None, weight='weight')
    plt.spy(L, markersize=2, color='black');
    return(L)

def show_circuit_graph(subgraph,filename,target):
    color_map = []

    plt.figure(figsize=(6, 8))
    for val in target:
        if val:
            color_map.append('red')
        else:
            color_map.append('green')
    pos = nx.spring_layout(subgraph)
    nx.draw(subgraph, node_color=color_map,pos=pos)
    plt.show()

    plt.figure(figsize=(6, 8))

    nx.draw(subgraph,pos=pos)
    plt.show()

def read_inputs(dir_path):
    print(dir_path)
    input_files = os.listdir(dir_path)
    node_keys=['inst_type','net_type','ports','edge_weight','values','sub_graph']
    graph_list={}
    for file in input_files:
        if file.endswith("yaml"):
            print("reading file",file)
            hier_graph=nx.Graph(nx.read_yaml(dir_path+file))
            print("no of nodes:",len(hier_graph.nodes()))
            feature_matrix=[]
            if not os.path.exists("train_data"):
                os.mkdir("train_data")
            csv_file='train_data/'+file[:-5]+'.csv'

            with open(csv_file, 'w') as writeFile:
                writer = csv.writer(writeFile)
                for node,attr in hier_graph.nodes(data=True):
                    #print(attr)
                    feature=[]
                    feature.append(node)
                    for node_key in node_keys:
                        if node_key not in attr:
                            feature.append('0')
                        elif node_key in ['inst_type']:
                            nbrs = [hier_graph.nodes[nd]['inst_type'] for nd in hier_graph.neighbors(node)]
                            if 'source' in attr['inst_type'] :
                                feature.append('0')
                            elif any('source' in nbr for nbr in nbrs) :
                                feature.append('0')
                            elif 'i0|' in node:
                                feature.append('2')
                            else:
                                feature.append('1')
                            feature.append(attr[node_key])

                        elif node_key in ['net_type','sub_graph']:
                            feature.append(attr[node_key])
                            #print(attr[node_key])
                        elif node_key =='ports':
                            feature.append(len(attr[node_key]))
                        elif node_key =='edge_weight':
                            feature.append(sum(attr[node_key]))
                        elif node_key == 'values':
                            feature.append(attr[node_key][-1])

                    feature_matrix.append(feature)
                writer.writerows(feature_matrix)
            data_pre={}
            data_pre = pd.read_csv(csv_file,names=['name','target']+node_keys)

            data_pre['values'],_=pd.factorize(data_pre['values'])
            if "NON_OTA" in csv_file:
                target=np.zeros(len(data_pre['values']))
            else:
                target=data_pre['target'].values.astype(np.float32)
            if 2 in target:
                targetnew = [1.0 if x == 2 else 0.0 for x in target]
                target =np.array(targetnew)
            print(target)

            data_pre.drop('target',axis=1)
            for node_key in ['inst_type','net_type','sub_graph']:
                one_hot = pd.get_dummies(data_pre[node_key])
                data_pre = data_pre.drop(node_key,axis = 1)
                data_pre = data_pre.join(one_hot,rsuffix=node_key)
            for node_key in ['values']:
                data_pre[node_key],_ = pd.factorize(data_pre[node_key])
            graph_list[file[:-5]] = {"data_matrix":data_pre,
                                      "target":target,
                                      "adjacency_matrix": nx.adjacency_matrix(hier_graph,weight='weight'),
                                      "hier_graph":hier_graph
                                      }
            #show_circuit_graph(hier_graph,file[:-5],target)
    return graph_list




#%%
if __name__ == '__main__':
    dir_path= "train_graphs/"
    input_dict=read_inputs(dir_path)
    #prepare_data(input_graph_dict)
    with open('processed_data.p', 'wb') as handle:
        pickle.dump(input_dict, handle, protocol=pickle.HIGHEST_PROTOCOL)
