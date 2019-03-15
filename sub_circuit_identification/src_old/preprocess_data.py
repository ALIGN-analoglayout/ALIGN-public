# -*- coding: utf-8 -*-
"""
Created on Fri Dec  7 13:19:45 2018

@author: kunal
"""

import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms import isomorphism
import numpy as np
#import panda as pd
import glob
import os,sys
import pickle
from util import max_connectivity,plt_graph


                    
#%%
def laplacian_matrix( graph):
    L = nx.laplacian_matrix(graph, nodelist=None, weight='weight')
    plt.spy(L, markersize=2, color='black');
    return(L) 
def read_inputs(dir_path):
    print(dir_path)
    input_files = os.listdir(dir_path)
    graph_list={}
    for file in input_files:
        if file.endswith("yaml"):
            hier_graph=nx.read_yaml(dir_path+file)
            #plt_graph(hier_graph,file[:-5])
            graph_list[file[:-5]] = {"nodes":hier_graph.nodes(data=True),
                                      "LAPLACIAN": laplacian_matrix(hier_graph)
                                      }       
    return graph_list

def prepare_data(graph_dict):
    for name in graph_dict:
        for node in graph_dict[name]:
            print(graph_dict[name])
   
if __name__ == '__main__':
    dir_path= "train_graphs/"
    input_graph_dict=read_inputs(dir_path)
    prepare_data(input_graph_dict)



#%%
'''

    with open('../../dataset/classification/' + DATASET +
              '/original/smiles_property.txt', 'r') as f:
        data_list = f.read().strip().split('\n')

    """Exclude the data contains "." in the smiles."""
    data_list = list(filter(lambda x:
                     '.' not in x.strip().split()[0], data_list))
    N = len(data_list)

    atom_dict = defaultdict(lambda: len(atom_dict))
    bond_dict = defaultdict(lambda: len(bond_dict))
    fingerprint_dict = defaultdict(lambda: len(fingerprint_dict))

    Molecules, Adjacencies, Properties = [], [], []

    for no, data in enumerate(data_list):

        print('/'.join(map(str, [no+1, N])))

        smiles, property = data.strip().split()

        mol = Chem.MolFromSmiles(smiles)
        atoms = create_atoms(mol)
        i_jbond_dict = create_ijbonddict(mol)

        fingerprints = create_fingerprints(atoms, i_jbond_dict, radius)
        Molecules.append(fingerprints)

        adjacency = create_adjacency(mol)
        Adjacencies.append(adjacency)

        property = np.array([int(property)])
        Properties.append(property)

    dir_input = ('../../dataset/classification/' + DATASET +
                 '/input/radius' + str(radius) + '/')
    os.makedirs(dir_input, exist_ok=True)

    np.save(dir_input + 'molecules', Molecules)
    np.save(dir_input + 'adjacencies', Adjacencies)
    np.save(dir_input + 'properties', Properties)

    dump_dictionary(fingerprint_dict, dir_input + 'fingerprint_dict.pickle')

    print('The preprocess has finished!')
    '''