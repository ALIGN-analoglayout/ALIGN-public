
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from collections import defaultdict
from itertools import chain, product
import re


class MNA:
    def __init__(self, n):
        self.n = n # number of voltages
        self.a = sp.dok_array( (n,n), dtype=np.float64)
        self.f = None
        self.b = None
        self.x = None
        self.xa = None
        self.g = []

        self.C = defaultdict(int)
        self.D = defaultdict(int)


    @property
    def m(self):
        shape = self.a.shape
        assert shape[0] == shape[1]
        return shape[0]

    def factor(self):
        self.f = sla.splu(self.a)

    def solve(self):
        m = self.m
        self.b = np.array([0]*m)
        for k,v in self.C.items():
            self.b[k] = v

        self.x = self.f.solve(self.b)

        self.d = np.array([0]*m)
        for k,v in self.D.items():
            self.d[k] = v

        print(self.d)

        self.xa = -self.f.solve(self.d, trans='T')
        
        #print('x:', self.x)
        #print('xa:', self.xa)


    def semantic(self):
        t1 = time.perf_counter_ns()
        self.a = self.a.tocsc()
        t2 = time.perf_counter_ns()
        self.factor()
        t3 = time.perf_counter_ns()
        self.solve()
        t4 = time.perf_counter_ns()
        print(f'convert: {(t2-t1)/1e9} factor: {(t3-t2)/1e9} solve: {(t4-t3)/1e9}')

    def add_g(self, i, j, g):
        assert i < self.n and j < self.n

        if i>=0:
            self.a[i, i] += g
        if j>=0:
            self.a[j, j] += g
        if i>=0 and j>=0:
            self.a[i, j] -= g
            self.a[j, i] -= g
 
        self.g.append( (i,j,g))

    def add_r(self, i, j, r):
        assert i < self.n and j < self.n

        m = self.m
        self.a.resize((m+1, m+1))

        if i >= 0:
            self.a[i, m] = 1
            self.a[m, i] = 1
        if j >= 0:
            self.a[j, m] = -1
            self.a[m, j] = -1

        self.a[m, m] = -r

    def add_c(self, i, c):
        self.C[i] += c

    def add_d(self, i, d):
        self.D[i] += d

    def sens_c(self, i):
        return -self.xa[i]

# x = A^-1 @ b
# xa^T = -d^T @ A^-1

# f = d^T @ x 
# dx/dh = - A^-1 @ (dA/dh @ x - db/dh)
# df/dh = d^T @ dx/dh

# df/dh = xa^T @ dA/dh @ x - xa^T @ db/dh

# df/dbi = - xa^T @ db/dbi
# db/dbi is one in position i of b, so we just grab the ith position of -xa

# df/drk = xa^T @ dA/drk @ x
# dA/drk is -1 in diagonal position k of A, so we just grab the kth position of xa and multiply it by -1 times the position k in x

# df/dgij = xa^T @ dA/dgij @ x
# dA/dgij is 1, -1, -1, 1 in positions ii, ij, ji, and jj, respectively, of A, so we just grab those position of xa and x and add/subtract the products.

    def sens_r(self, k):
        return - self.xa[k] * self.x[k]

    def sens_g(self, k):
        i, j, _ = self.g[k]

        result = 0.0

        if i>=0:
            result += self.xa[i]*self.x[i]
        if j>=0:
            result += self.xa[j]*self.x[j]
        if i>=0 and j>=0:
            result -= self.xa[i]*self.x[j]
            result -= self.xa[j]*self.x[i]

        return result

    def rel_sens_c(self, i):
        return self.sens_c(i) * self.b[i] / self.objective()

    def rel_sens_r(self, k):
        return self.sens_r(k) * -self.a[k, k] / self.objective()

    def rel_sens_g(self, k):
        _, _, g = self.g[k]
        return self.sens_g(k) * g / self.objective()

    def objective(self):
        return self.d.dot(self.x)

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


    

