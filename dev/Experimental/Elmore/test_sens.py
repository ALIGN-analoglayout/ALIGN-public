
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from collections import defaultdict
from itertools import chain, product
import re

from mna import MNA

def gen_chain_g(n, delta_k=None, delta_g=0.0):
    G = MNA(n)

    G.add_d(n-1, 1)

    t0 = time.perf_counter_ns()
    for i in range(n):
        G.add_g(i-1, i, 1+delta_g if delta_k is not None and i == delta_k else 1)
        G.add_c(i, 1)
    t1 = time.perf_counter_ns()
    print(f'build: {(t1-t0)/1e9}')

    G.semantic()
    return G

def test_sens_g():

    for n in [2, 4, 100]:
        G = gen_chain_g(n)
        center = G.objective()
        print('sens to g:', [G.sens_g(k) for k in range(len(G.g))])
        print('rel sens to g:', [G.rel_sens_g(k) for k in range(len(G.g))])
        for k in range(n):
            delta_h = 0.001
            Gd = gen_chain_g(n, delta_k=k, delta_g=delta_h)
            delta_f = Gd.objective() - center
            delta_f_predict = G.sens_g(k) * delta_h

            print(f'{Gd.objective()}-{center} = {delta_f} ({delta_f_predict})')

            assert abs(delta_f - delta_f_predict) <= abs(delta_f) * delta_h * 2, (delta_f, delta_f_predict, delta_f-delta_f_predict)


def gen_chain_r(n, delta_k=None, delta_r=0.0):

    G = MNA(n)

    G.add_d(n-1, 1)

    t0 = time.perf_counter_ns()
    for i in range(n):
        G.add_r(i-1, i, 1+delta_r if delta_k is not None and i == delta_k else 1)
        G.add_c(i, 1)

    t1 = time.perf_counter_ns()
    print(f'build: {(t1-t0)/1e9}')

    G.semantic()
    return G

def test_sens_r():
    for n in [2, 4, 100]:
        G = gen_chain_r(n, delta_k=None, delta_r=0)
        center =  G.objective()
        print('sens to r:', [G.sens_r(k) for k in range(G.n, G.m)])
        print('rel sens to r:', [G.rel_sens_r(k) for k in range(G.n, G.m)])

        for k in range(n):
            delta_h = 0.001
            Gd = gen_chain_r(n, delta_k=k, delta_r=delta_h)
            delta_f = Gd.objective()-center
            delta_f_predict = G.sens_r(k+G.n) * delta_h

            print(f'{Gd.objective()}-{center} = {delta_f} ({delta_f_predict})')

            assert abs(delta_f - delta_f_predict) <= abs(delta_f) * delta_h * 2, (delta_f, delta_f_predict, delta_f-delta_f_predict)

# n=2; f = R1*(C1+C2) + R2*C2
# df/dC1 = R1; df/dC2 = R1+R2; df/dR1 = C1+C2; df/dR2 = C2 


    

