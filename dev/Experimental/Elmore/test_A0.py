
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from collections import defaultdict
from itertools import chain, product
import re


class Route:
    def __init__(self):
        self.driver_terminals = []
        self.receiver_terminals = []

        self.wires = []

        self.raster = defaultdict(set)

        self.segments = set()


    @staticmethod
    def build_wire(rect, layer):
        return {'rect': rect, 'layer': layer}
    

    def semantic(self):
        for ty, wire in chain(product(['driver'],self.driver_terminals),
                              product(['receiver'],self.receiver_terminals),
                              product(['wire'],self.wires)):
            llx, lly, urx, ury = wire['rect']
            l = wire['layer']
            if llx < urx:
                assert lly == ury
                for x in range(llx, urx+1):
                    self.raster[(x,lly)].add((ty,l))
                for x in range(llx, urx):
                    self.segments.add(((x,lly,l),(x+1,lly,l)))
            elif lly < ury:
                assert llx == urx
                for y in range(lly, ury+1):
                    self.raster[(llx,y)].add((ty,wire['layer']))
                for y in range(lly, ury):
                    self.segments.add(((llx,y,l), (llx,y+1,l)))
            else:
                assert llx == urx and lly == ury
                self.raster[(llx,lly)].add((ty,wire['layer']))

        p = re.compile(r'^M(\d+)$')

        def next_layer(ly):
            m = p.match(ly)
            assert m is not None
            n = int(m.groups()[0])
            return f'M{n+1}'

        for k, lst in self.raster.items():
            x, y = k
            s = set(l for _, l in lst)
            for l in s:
                nl = next_layer(l)
                if nl in s:
                    self.segments.add( ( (x,y,l), (x,y,nl) ) )


    def build_network(self):

        c_values = { 'M1': 0.2, 'M2': 0.2, 'M3': 0.2 }

        r_values = { 'M1': 50, 'M2': 50, 'M3': 50, ('M1', 'M2'): 25, ('M2', 'M3'): 25 }

        directions = { 'M1': 'V', 'M2': 'H', 'M3': 'V' }

        distances = { 'V': 0.80, 'H': 0.84 } # microns per grid

        def layer2dist(ly):
            return distances[directions[ly]]

        nodes = set()
        for t0, t1 in self.segments:
            nodes.add(t0)
            nodes.add(t1)

        nodes_alt = set()
        for k, lst in self.raster.items():
            x, y = k
            for ty, l in lst:
                nodes_alt.add( (x,y,l))

        assert nodes == nodes_alt

        resistors = []
        capacitors = defaultdict(int)

        for t0, t1 in self.segments:
            x0, y0, l0 = t0
            x1, y1, l1 = t1

            if l0 != l1: # via
                r = r_values[(l0,l1)]
                resistors.append((t0,t1,r))
                
            else:
                r = r_values[l0] * layer2dist(l0)
                c = c_values[l0] * layer2dist(l0)

                resistors.append((t0,t1,r))
                capacitors[t0] += c/2
                capacitors[t1] += c/2


        nodes_a = list(nodes)
        node_mapping = {t: i for i, t in enumerate(nodes_a)}

        g = MNA(len(nodes_a))

        for t0, t1, r in resistors:
            g.add_r( node_mapping[t0], node_mapping[t1], r)

        for t, c in capacitors.items():
            g.add_c(node_mapping[t], c)


        for k, lst in self.raster.items():
            for ty, l in lst:
                if ty == 'driver':
                    t = k[0], k[1], l
                    g.add_r( -1, node_mapping[t], 0)

        receiver_count = sum(1 for k, lst in self.raster.items() for ty, _ in lst if ty == 'receiver')

        for k, lst in self.raster.items():
            for ty, l in lst:
                if ty == 'receiver':
                    t = k[0], k[1], l
                    g.add_d( node_mapping[t], 1/receiver_count)


        g.semantic()
        print('Obj:', g.objective())


def build_example():
    r = Route()
    
    # driver terminals
    r.driver_terminals.append(Route.build_wire([1,1,1,1], 'M1'))
    r.driver_terminals.append(Route.build_wire([2,1,2,1], 'M1'))
    r.driver_terminals.append(Route.build_wire([3,1,3,1], 'M1'))

    r.driver_terminals.append(Route.build_wire([1,2,1,2], 'M1'))
    r.driver_terminals.append(Route.build_wire([2,2,2,2], 'M1'))
    r.driver_terminals.append(Route.build_wire([3,2,3,2], 'M1'))

    # receiver terminals
    r.receiver_terminals.append(Route.build_wire([6,4,6,4], 'M1'))
    r.receiver_terminals.append(Route.build_wire([7,4,7,4], 'M1'))
    r.receiver_terminals.append(Route.build_wire([8,4,8,4], 'M1'))

    r.receiver_terminals.append(Route.build_wire([6,5,6,5], 'M1'))
    r.receiver_terminals.append(Route.build_wire([7,5,7,5], 'M1'))
    r.receiver_terminals.append(Route.build_wire([8,5,8,5], 'M1'))

    # primitive wiring
    r.wires.append(Route.build_wire([1,1,3,1], 'M2')) 
    r.wires.append(Route.build_wire([1,2,3,2], 'M2')) 

    r.wires.append(Route.build_wire([6,4,8,4], 'M2')) 
    r.wires.append(Route.build_wire([6,5,8,5], 'M2')) 

    return r

def test_example_route0():
    
    """
   
5                            X----X----X
                             |
                             |
4             +--------------X----X----X
              |
              |
3             |
              |
              | 
2   X----X----X
              |
              |
1   X----X----X


    1    2    3    4    5    6    7    8
"""

    t0 = time.perf_counter_ns()
    r = build_example()
    r.wires.append(Route.build_wire([3,4,6,4], 'M2')) 
    r.wires.append(Route.build_wire([3,1,3,4], 'M3'))
    r.wires.append(Route.build_wire([6,4,6,5], 'M3'))
    t1 = time.perf_counter_ns()
    print(f'build: {(t1-t0)/1e9}')

    r.semantic()

    t0 = time.perf_counter_ns()
    r.build_network()
    t1 = time.perf_counter_ns()
    print(f'build_network: {(t1-t0)/1e9}')

def test_example_route1():
    
    """
   
5                            X----X----X
                                  |
                                  |
4             +--------------X----X----X
              |
              |
3             |
              |
              | 
2   X----X----X
              |
              |
1   X----X----X


    1    2    3    4    5    6    7    8
"""

    t0 = time.perf_counter_ns()
    r = build_example()
    r.wires.append(Route.build_wire([3,4,6,4], 'M2')) 
    r.wires.append(Route.build_wire([3,1,3,4], 'M3'))
    r.wires.append(Route.build_wire([7,4,7,5], 'M3'))
    t1 = time.perf_counter_ns()
    print(f'build: {(t1-t0)/1e9}')

    r.semantic()

    t0 = time.perf_counter_ns()
    r.build_network()
    t1 = time.perf_counter_ns()
    print(f'build_network: {(t1-t0)/1e9}')

def test_example_route2():
    
    """
   
5                            X----X----X
                                  |
                                  |
4                            X----X----X
                                  |
                                  |
3                                 |
                                  |
                                  |
2   X----X----X-------------------+
                                  |
                                  |
1   X----X----X-------------------+


    1    2    3    4    5    6    7    8
"""

    t0 = time.perf_counter_ns()
    r = build_example()
    r.wires.append(Route.build_wire([3,1,7,1], 'M2')) 
    r.wires.append(Route.build_wire([3,2,7,2], 'M2')) 
    r.wires.append(Route.build_wire([7,1,7,5], 'M3'))
    t1 = time.perf_counter_ns()
    print(f'build: {(t1-t0)/1e9}')

    r.semantic()

    t0 = time.perf_counter_ns()
    r.build_network()
    t1 = time.perf_counter_ns()
    print(f'build_network: {(t1-t0)/1e9}')



class MNA:
    def __init__(self, n):
        self.n = n # number of voltages
        self.a = sp.dok_array( (n,n), dtype=np.float64)
        self.f = None
        self.b = None
        self.x = None
        self.xa = None
        self.g = []

        self.C = [0]*self.n
        self.D = [0]*self.n


    @property
    def m(self):
        shape = self.a.shape
        assert shape[0] == shape[1]
        return shape[0]

    def factor(self):
        self.f = sla.splu(self.a)

    def solve(self):
        m = self.a.shape[0]
        self.b = np.array(self.C + [0]*(m - self.n))
        self.x = self.f.solve(self.b)

        self.d = np.array(self.D + [0]*(m - self.n))
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

        m = self.a.shape[0]
        self.a.resize((m+1, m+1))

        if i >= 0:
            self.a[i, m] = 1
            self.a[m, i] = 1
        if j >= 0:
            self.a[j, m] = -1
            self.a[m, j] = -1

        self.a[m, m] = -r

    def add_c(self, i, c):
        assert 0 <= i < self.n
        self.C[i] += c

    def add_d(self, i, d):
        assert 0 <= i < self.n
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
        i, j, g = self.g[k]

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


    

