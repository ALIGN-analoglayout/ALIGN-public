from collections import defaultdict, Counter
import random
import render
import argparse
import re

import heapq

class Lee:
    def __init__(self, n, m):
        self.n, self.m = n, m
        self.paths = {}
        self.via_cost = 10

        self.sum_of_counts = 0


    def add_path(self, nm, path):
        self.paths[nm] = path

    def show(self):

        h_edges = defaultdict(set)
        v_edges = defaultdict(set)

        for nm, path in self.paths.items():
            for p0, p1 in zip(path[:-1], path[1:]):
                i0, i1 = min(p0[0], p1[0]), max(p0[0], p1[0])
                j0, j1 = min(p0[1], p1[1]), max(p0[1], p1[1])
                k0, k1 = min(p0[2], p1[2]), max(p0[2], p1[2])
                if k0 != k1: # via
                    assert k0 + 1 == k1
                elif i0 == i1: # h_edge
                    assert j0 + 1 == j1
                    h_edges[((i0,j0),(i1,j1))].add(nm)
                elif j0 == j1: # v_edge
                    assert i0 + 1 == i1
                    v_edges[((i0,j0),(i1,j1))].add(nm)
                else:
                    assert False, (p0, p1)

        def h_edge_on( i, j):
            return h_edges[((i,j),(i,j+1))]

        def v_edge_on( i, j):
            return v_edges[((i,j),(i+1,j))]

        render.show(self.n, self.m, h_edge_on, v_edge_on)


    def path2str(self, path):
        s = []
        for u, v in zip(path[:-1], path[1:]):
            if u[2] != v[2]: # via
                assert u[0] == v[0] and u[1] == v[1]
                if u[2]+1 == v[2]: # up
                    s.append('+')
                elif u[2]-1 == v[2]: # down
                    s.append('-')
                else:
                    assert False
            elif u[0] == v[0]: # horizontal
                if u[1]+1 == v[1]: # right
                    s.append('R')
                elif u[1]-1 == v[1]: # left
                    s.append('L')
                else:
                    assert False
            elif u[1] == v[1]: # vertical
                if u[0]+1 == v[0]: # down
                    s.append('D')
                elif u[0]-1 == v[0]: # up
                    s.append('U')
                else:
                    assert False
            else:
                assert False

        return ''.join(s)

    def _astar(self, nm, src, tgt, obstacles=None, heuristic=(lambda v: 0)):

        if obstacles is None:
            obstacles_s = set()
        else:
            obstacles_s = obstacles
        
        def adjacent_states(u):
            i, j, k = u

            if k == 0: # vertical
                next_states = [(i-1,j,0),(i+1,j,0),(i,j,1)]

            elif k == 1: # horizontal
                next_states = [(i,j-1,1),(i,j+1,1),(i,j,0)]
            else:
                assert False

            for ii, jj, kk in next_states:
                if 0 <= ii < self.n and 0 <= jj < self.m and 0 <= kk < 2 and (ii, jj) not in obstacles_s:
                    yield (ii, jj, kk), (self.via_cost if kk != k else 1)


        src0 = src[0], src[1], 0
        src1 = src[0], src[1], 1

        tgt0 = tgt[0], tgt[1], 0
        tgt1 = tgt[0], tgt[1], 1

        dist = {src0 : 0, src1 : 0}

        came_from = {src0 : None, src1 : None}

        q = [(0, src0), (0, src1)]

        heapq.heapify(q)

        count = 0

        while q:
            count += 1
            _, u = heapq.heappop(q)

            if u == tgt0 or u == tgt1:
                path = [u]
                while (u := came_from[u]) is not None:
                    path.append(u)
                path.reverse()

                self.sum_of_counts += count

                return path

            for v, weight in adjacent_states(u):
                alt = dist[u] + weight
                if v not in dist or alt < dist[v]:
                    dist[v] = alt
                    priority = alt + heuristic(v)
                    heapq.heappush(q, (priority, v))
                    came_from[v] = u

        return None


    def dijkstra(self, nm, src, tgt, obstacles=None):
        return self._astar(nm, src, tgt, obstacles=obstacles)


    def astar(self, nm, src, tgt, obstacles=None):
        def heuristic(v):
            delta_i = abs(tgt[0] - v[0])
            delta_j = abs(tgt[1] - v[1])

            res = delta_i + delta_j
            
            # k=1 is horizontal
            if v[2] == 1 and delta_i != 0 or \
               v[2] == 0 and delta_j != 0:
                res += self.via_cost

            # causes failures
            #res += random.randrange(0, 11)

            return res

        return self._astar(nm, src, tgt, obstacles=obstacles, heuristic=heuristic)

    def route_all(self, lst, alg='astar', check=False):

        fn = self.astar if alg == 'astar' else self.dijkstra

        all_ok = True

        print("="*80)

        obstacles = set()

        for _, src, tgt in lst:
            obstacles.add(src)
            obstacles.add(tgt)

        for nm, src, tgt in lst:
            obstacles.remove(src)
            obstacles.remove(tgt)

            path_l = fn( nm, src, tgt, obstacles=obstacles)
            if check:
                path_l_ref = self.dijkstra( nm, src, tgt, obstacles=obstacles)
                assert (path_l is None) == (path_l_ref is None)

                if path_l is not None:
                    pl, pl_ref = self.path_length(path_l), self.path_length(path_l_ref)
                    #print(f'Checking path lengths: {alg} {pl} dijkstra {pl_ref}')
                    assert pl == pl_ref

            if path_l is None:
                obstacles.add(src)
                obstacles.add(tgt)
                all_ok = False
            else:
                obstacles.update([(tup[0], tup[1]) for tup in path_l])
                self.add_path(nm, path_l)

            print(nm, src, tgt, self.path2str(path_l) if path_l is not None else None)

        return all_ok

    def path_length(self, path):
        ss = 0
        assert len(path) >= 1
        i0, j0, k0 = path[0]
        for i1, j1, k1 in path[1:]:
            ss += self.via_cost if k0 != k1 else 1
            i0, j0, k0 = i1, j1, k1 
        return ss

    def total_wire_length(self):
        return sum(self.path_length(path) for _, path in self.paths.items())
        

def main(n, m, lst, num_trials, alg='astar', check=False):
    count = 0
    histo = Counter()
    for _ in range(num_trials):
        samp = random.sample(lst, len(lst))
        a = Lee(n, m)
        ok = a.route_all(samp, alg=alg, check=check)
        if ok:
            print(f'Routed all {len(lst)} nets. Wire Length = {a.total_wire_length()} Dequeues: {a.sum_of_counts}')
            count += 1
            histo[a.total_wire_length()] += 1
        else:
            print(f'Only routed {len(a.paths)} of {len(lst)} nets.')

        a.show()
    print(f'Successfull routed {count} of {num_trials} times.')
    print(f'Wirelength histogram:', list(sorted(histo.items())))


def test_total_wire_length():
    a = Lee(4, 4)

    a.paths['0'] = [(0,0,0), (0,1,0), (0,1,1), (1,1,1)]
    a.via_cost = 10
    assert a.total_wire_length() == 12

    a.via_cost = 0
    assert a.total_wire_length() == 2


if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Lee Router")
    parser.add_argument("-m", "--model", type=str, default="ten_nets_8x8")
    parser.add_argument("-n", "--num_trials", type=int, default=100)
    parser.add_argument("-a", "--alg", type=str, default='astar')
    parser.add_argument("-s", "--seed", type=int, default=0)
    parser.add_argument("-c", "--check", action='store_true')

    args = parser.parse_args()

    random.seed(args.seed)

    """
  01234567
 +--------
0|  1  8  
1|     5
2|12 6  78
3|2   79
4|      6
5|3   54
6| 4    9a
7|  3  a
"""

    ten_nets = [
        ("1", (2, 0), (0, 2)),
        ("2", (3, 0), (2, 1)),
        ("3", (5, 0), (7, 2)),
        ("4", (6, 1), (5, 5)),
        ("5", (5, 4), (1, 5)),
        ("6", (2, 3), (4, 6)),
        ("7", (3, 4), (2, 6)),
        ("8", (0, 5), (2, 7)),
        ("9", (3, 5), (6, 6)),
        ("a", (7, 5), (6, 7)),
    ]

    simple_nets = [
        ("3", (5, 0), (7, 2)),
        ("4", (6, 1), (5, 5)),
    ]

    def scale(nets, scale=1):
        for net, src, tgt in nets:
            yield net, tuple(x*scale for x in src), tuple(x*scale for x in tgt)

    p = re.compile(r'^(ten_nets|simple)_(\d+)x(\d+)$')

    m = p.match(args.model)

    if m:
        subs = m.groups()
        n_i = int(subs[1])
        n_j = int(subs[2])
        assert n_i == n_j
        nets = ten_nets if subs[0] == 'ten_nets' else simple_nets

        factor = (n_i+7) // 8

        main(n_i, n_j, list(scale(nets, factor)), num_trials=args.num_trials, alg=args.alg, check=args.check)        

    elif args.model == "two_nets_10x10":
        main(10, 10, [("a", (3,2), (7,6)), ("b", (6,4), (2,8))], num_trials=args.num_trials, alg=args.alg, check=args.check)

    elif args.model == "river_8x8":
        main(8, 8, [
        ("0", (7, 0), (0, 7)),
        ("1", (7, 1), (1, 7)),
        ("2", (7, 2), (2, 7)),
        ("3", (7, 3), (3, 7)),
        ("4", (7, 4), (4, 7)),
        ("5", (7, 5), (5, 7)),
        ("6", (7, 6), (6, 7)),
        ], num_trials=args.num_trials, alg=args.alg, check=args.check)

    elif args.model == "synthetic_4x20":
        main(4, 20, [
        ("a", (1, 0), (3, 2)),
        ("A", (2, 1), (0, 3)),
        ("b", (1, 4), (3, 6)),
        ("B", (2, 5), (0, 7)),
        ("c", (1, 8), (3, 10)),
        ("C", (2, 9), (0, 11)),
        ("d", (1, 12), (3, 14)),
        ("D", (2, 13), (0, 15)),
        ("e", (1, 16), (3, 18)),
        ("E", (2, 17), (0, 19)),
        ], num_trials=args.num_trials, alg=args.alg, check=args.check)

    elif args.model == "synthetic_4x16":
        main(4, 16, [
        ("a", (1, 0), (3, 2)),
        ("A", (2, 1), (0, 3)),
        ("b", (1, 4), (3, 6)),
        ("B", (2, 5), (0, 7)),
        ("c", (1, 8), (3, 10)),
        ("C", (2, 9), (0, 11)),
        ("d", (1, 12), (3, 14)),
        ("D", (2, 13), (0, 15)),
        ], num_trials=args.num_trials, alg=args.alg, check=args.check)

    elif args.model == "synthetic_4x12":
        main(4, 12, [
        ("a", (1, 0), (3, 2)),
        ("A", (2, 1), (0, 3)),
        ("b", (1, 4), (3, 6)),
        ("B", (2, 5), (0, 7)),
        ("c", (1, 8), (3, 10)),
        ("C", (2, 9), (0, 11)),
        ], num_trials=args.num_trials, alg=args.alg, check=args.check)

    else:
        assert False, f"Unknown model: {args.model}"
