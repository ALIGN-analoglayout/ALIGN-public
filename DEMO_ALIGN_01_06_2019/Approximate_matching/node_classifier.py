# -*- coding: utf-8 -*-
"""
Created on Fri Nov 16 15:05:06 2018

@author: kunal
"""

from src import models, graph, coarsening, utils
import numpy as np
import pickle
import networkx as nx
import matplotlib.pyplot as plt
from scipy.sparse import csr_matrix, block_diag, csgraph, coo_matrix
from scipy.sparse.csgraph import csgraph_from_dense
#%matplotlib inline
#d : Dimensionality/feature.
#n : Number of samples.
#c : Number of feature communities.

# Data matrix, structured in communities (feature-wise).

with open('processed_data.p', 'rb') as fp:
    all_inputs = pickle.load(fp)
if 'circuit_graph' in locals(): del circuit_graph
for circuit_name,circuit_data in all_inputs.items():
    if 'circuit_graph' in locals() and 'X' in locals():
        df=circuit_data["data_matrix"]
        print(circuit_name)
        input_data=df.values
        input_data=np.delete(input_data,0,1)
        input_data=np.array(input_data,dtype=np.float32)
        input_data=input_data[:,0:16]
        X=np.concatenate((X,input_data), axis=0)
        label=circuit_data["target"].reshape((-1, 1))
        y=np.concatenate((y,label), axis=0)
        igraph=circuit_data["adjacency_matrix"]
        circuit_graph=block_diag((circuit_graph,igraph)).tocsr()
        #show_graph_with_labels(igraph)

        #print("graph shape:",circuit_graph.shape)
    else:
        df=circuit_data["data_matrix"]
        input_data=df.values
        input_data=np.delete(input_data,0,1)
        input_data=np.array(input_data,dtype=np.float32)
        input_data=input_data[:,0:16]
        X=input_data
        y=circuit_data["target"].reshape((-1, 1))
        #print(y.shape)
        circuit_graph=circuit_data["adjacency_matrix"]
        #print(circuit_graph)
        #show_graph_with_labels(circuit_graph)
def show_graph_with_labels(adjacency_matrix):
    plt.figure(figsize=(3,4))
    G=nx.Graph(adjacency_matrix)
    nx.draw(G)
    plt.show()
print("feature",X.shape)

y=y.reshape(-1)
#circuit_graph= np.delete(circuit_graph, 0, 0)
print("graph shape",circuit_graph.shape)
#print("graph shape:",circuit_graph.toarray())
n,d=X.shape
print("shape",n,d)
# Noisy non-linear target.
w = np.random.normal(0, .02, d)
t = X.dot(w)
#print(t.shape)
t = np.tanh(t)
plt.figure(figsize=(15, 5))
plt.plot(t, '.')
plt.savefig("spectrum.png")
# Classification.
#y = np.ones(t.shape, dtype=np.uint8)
#y[t > t.mean() + 0.4 * t.std()] = 0
#y[t < t.mean() - 0.4 * t.std()] = 2
print('Class imbalance: ', np.unique(y, return_counts=True)[1])
n_train = n // 3
n_val = n // 10

X_train = X[:n_train]
X_val   = X[n_train:n_train+n_val]
X_test  = X[n_train+n_val:]
#print("X_train",X_train)
y_train = y[:n_train]
y_val   = y[n_train:n_train+n_val]
y_test  = y[n_train+n_val:]

A=circuit_graph.astype(np.float32)

assert A.shape == (n,n)
print('d = |V| = {}, k|V| < |E| = {}'.format(d, A.nnz))
plt.spy(A, markersize=2, color='black')

graphs, perm = coarsening.coarsen(A, levels=3, self_connections=False)

X_train = coarsening.perm_data(X_train, perm)
X_val = coarsening.perm_data(X_val, perm)
X_test = coarsening.perm_data(X_test, perm)
#for A in graphs:
#    show_graph_with_labels(A)

L = [graph.laplacian(A, normalized=True) for A in graphs]
#L = [csgraph.laplacian(A, normed=True).tocsr() for A in graphs]
graph.plot_spectrum(L)
del A

# %%

params = dict()
params['dir_name']       = 'demo'
params['num_epochs']     = 50
params['batch_size']     = 10
params['eval_frequency'] = 5

# Building blocks.
params['filter']         = 'chebyshev5'
params['brelu']          = 'b1relu'
params['pool']           = 'apool1'

# Number of classes.
C = y.max() + 1
assert C == np.unique(y).size

# Architecture.
params['F']              = [32, 64]  # Number of graph convolutional filters.
params['K']              = [20, 20]  # Polynomial orders.
params['p']              = [4, 2]    # Pooling sizes.
params['M']              = [512, C]  # Output dimensionality of fully connected layers.

# Optimization.
params['regularization'] = 5e-4
params['dropout']        = 1
params['learning_rate']  = 1e-3
params['decay_rate']     = 0.95
params['momentum']       = 0.9
params['decay_steps']    = n_train / params['batch_size']
model = models.cgcnn(L, **params)
accuracy, loss, t_step = model.fit(X_train, y_train, X_val, y_val)
fig, ax1 = plt.subplots(figsize=(15, 5))
ax1.plot(accuracy, 'b.-')
ax1.set_ylabel('validation accuracy', color='b')
ax2 = ax1.twinx()
ax2.plot(loss, 'g.-')
ax2.set_ylabel('training loss', color='g')
plt.savefig("accuracyr_vs_epoch.png")
print('Time per step: {:.2f} ms'.format(t_step*1000))
xyzz1 = input('Running Test Cases')
string, test_accuracy, test_f1, test_loss = model.evaluate(X_test,y_test)
print('test  {}'.format(string))
