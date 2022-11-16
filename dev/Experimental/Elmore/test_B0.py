
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from collections import defaultdict
from itertools import chain, product
import re

from mna import MNA



def test_B0():

    g = MNA( 4)

    R1, R2, R3, R4 = 1, 1, 1, 1

    g.add_r( 0, 1, R1)
    g.add_r( 0, 3, R2)
    g.add_r( 2, 1, R3)
    g.add_r( 2, 3, R4)
    g.add_r(-1, 3,  0)

    g.add_c( 0, 50)
    g.add_c( 1, -30)
    g.add_c( 2, 40)

    g.semantic()

    print(g.a.todense())

    print(g.x)

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
