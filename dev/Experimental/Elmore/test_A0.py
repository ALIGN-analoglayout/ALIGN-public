
import time

from route import Route, build_example

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



