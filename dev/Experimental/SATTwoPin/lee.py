from collections import defaultdict, Counter
import random
import render
import argparse

import heapq

class Lee:
    def __init__(self, n, m):
        self.n, self.m = n, m
        self.paths = {}

    def add_path(self, nm, path):
        self.paths[nm] = path

    def show(self):

        h_edges = defaultdict(set)
        v_edges = defaultdict(set)

        for nm, path in self.paths.items():
            for p0, p1 in zip(path[:-1], path[1:]):
                i0, i1 = min(p0[0], p1[0]), max(p0[0], p1[0])
                j0, j1 = min(p0[1], p1[1]), max(p0[1], p1[1])
                if i0 == i1: # h_edge
                    assert j0 + 1 == j1
                    h_edges[((i0,j0),(i1,j1))].add(nm)
                elif j0 == j1: # v_edge
                    assert i0 + 1 == i1
                    v_edges[((i0,j0),(i1,j1))].add(nm)

        def h_edge_on( i, j):
            return h_edges[((i,j),(i,j+1))]

        def v_edge_on( i, j):
            return v_edges[((i,j),(i+1,j))]

        render.show(self.n, self.m, h_edge_on, v_edge_on)


    def path2str(self, path):
        s = []
        for u, v in zip(path[:-1], path[1:]):
            if u[0] == v[0]: # horizontal
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

        return ''.join(s)

    def _astar(self, nm, src, tgt, obstacles=None, heuristic=(lambda v: 0)):

        if obstacles is None:
            obstacles_s = set()
        else:
            obstacles_s = obstacles
        
        def adjacent_states(u):
            i, j = u
            for ii, jj in [(i-1,j), (i+1,j), (i,j-1), (i, j+1)]:
                if 0 <= ii < self.n and 0 <= jj < self.m and (ii, jj) not in obstacles_s:
                    yield (ii, jj), 1


        dist = {src : 0}

        came_from = {src : None}

        q = [(0, src)]

        heapq.heapify(q)


        count = 0
        found = False



        print(f'Working on {nm}...')

        while q:

            count += 1

            p, u = heapq.heappop(q)

            print(f'Top: {(p, u)}')

            if u == tgt:
                found = True
                break

            w = came_from[u]
            for v, weight in adjacent_states(u):
                if w is not None:
                    if v[0] == u[0] and u[0] == w[0] or \
                       v[1] == u[1] and u[1] == w[1]:
                        pass
                    else:
                        weight += 10

                alt = dist[u] + weight
                if v not in dist or alt < dist[v]:
                    dist[v] = alt
                    priority = alt + heuristic(v)
                    print(f'Enqueueing {(priority, v)}')
                    heapq.heappush(q, (priority, v))
                    came_from[v] = u

        if found:

            assert tgt in dist

            u = tgt
            path = [u]
            while u != src:
                u = came_from[u]
                path.append(u)

            path.reverse()

            return self.path2str(path), path
        else:
            return None, None

    def dijkstra(self, nm, src, tgt, obstacles=None):
        return self._astar(nm, src, tgt, obstacles=obstacles)


    def astar(self, nm, src, tgt, obstacles=None):
        def heuristic(v):
            return sum(abs(tgt[i] - v[i]) for i in range(2))

        return self._astar(nm, src, tgt, obstacles=obstacles, heuristic=heuristic)


    def bfs(self, nm, src, tgt, obstacles=None):

        if obstacles is None:
            obstacles_s = set()
        else:
            obstacles_s = obstacles

        def adjacent_states(u):
            i, j = u
            for ii, jj in [(i-1,j), (i+1,j), (i,j-1), (i, j+1)]:
                if 0 <= ii < self.n and 0 <= jj < self.m and (ii, jj) not in obstacles_s:
                    yield (ii, jj), 1


        reached = {}

        frontier = { src }

        came_from = {src : None}


        found = False
        count = 0
        while frontier:
            new_frontier = set()
            for u in frontier:
                for v, _ in adjacent_states(u):
                    if v not in new_frontier and v not in reached:
                        came_from[v] = u
                    new_frontier.add(v)
                    if v == tgt:
                        found = True

            for u in frontier:
                reached[u] = count

            count += 1

            if found:
                reached[tgt] = count
                break

            frontier = set()
            for u in new_frontier:
                if u not in reached:
                    frontier.add(u)

            #print( f'count: {count} |frontier|: {len(frontier)} |reached|: {len(reached)}')

    
        if found:
            u = tgt
            path = [u]
            while u != src:
                u = came_from[u]
                path.append(u)

            path.reverse()

            return self.path2str(path), path
        else:
            return None, None


    def route_all(self, lst, alg='bfs'):

        fn = self.bfs if alg == 'bfs' else (self.astar if alg == 'astar' else self.dijkstra)

        all_ok = True

        print("="*80)

        obstacles = set()

        for _, src, tgt in lst:
            obstacles.add(src)
            obstacles.add(tgt)

        for nm, src, tgt in lst:
            obstacles.remove(src)
            obstacles.remove(tgt)

            path_s, path_l = fn( nm, src, tgt, obstacles=obstacles)

            if path_l is None:
                obstacles.add(src)
                obstacles.add(tgt)
                all_ok = False
            else:
                obstacles.update(path_l)
                self.add_path(nm, path_l)

            print(nm, src, tgt, path_s, path_l)

        return all_ok

    def total_wire_length(self, bend_cost=10):
        s = 0
        for _, path in self.paths.items():
            assert len(path) >= 2
            ss = 1
            x0, y0 = path[0]
            x1, y1 = path[1]
            for x2, y2 in path[2:]:
                ss += 1
                if x0 == x1 and x1 == x2 or y0 == y1 and y1 == y2:
                    pass
                else:
                    ss += bend_cost
                x0, y0 = x1, y1
                x1, y1 = x2, y2
            s += ss
        return s
        

def main(n, m, lst, num_trials, alg='bfs'):
    count = 0
    histo = Counter()
    for _ in range(num_trials):
        samp = random.sample(lst, len(lst))
        a = Lee(n, m)
        ok = a.route_all(samp, alg=alg)
        if ok:
            print(f'Routed all {len(lst)} nets. Wire Length = {a.total_wire_length()}')
            count += 1
            histo[a.total_wire_length()] += 1
        else:
            print(f'Only routed {len(a.paths)} of {len(lst)} nets.')

        a.show()
    print(f'Successfull routed {count} of {num_trials} times.')
    print(f'Wirelength histogram:', list(sorted(histo.items())))


def test_total_wire_length():
    a = Lee(4, 4)

    a.paths['0'] = [(0,0), (0,1), (1,1)]

    assert a.total_wire_length(bend_cost=0) == 2
    assert a.total_wire_length(bend_cost=10) == 12


if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Lee Router")
    parser.add_argument("-m", "--model", type=str, default="ten_nets_8x8")
    parser.add_argument("-n", "--num_trials", type=int, default=100)
    parser.add_argument("-a", "--alg", type=str, default='bfs')

    args = parser.parse_args()

    if args.model == "two_nets_10x10":
        main(10, 10, [("a", (3,2), (7,6)), ("b", (6,4), (2,8))], num_trials=args.num_trials, alg=args.alg)

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

    elif args.model == "ten_nets_8x8":

        main(8, 8, [
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
        ], num_trials=args.num_trials, alg=args.alg)


    elif args.model == "ten_nets_16x16":
        main(16, 16, [
        ("1", (4, 0), (0, 4)),
        ("2", (6, 0), (4, 2)),
        ("3", (10, 0), (14, 4)),
        ("4", (12, 2), (10, 10)),
        ("5", (10, 8), (2, 10)),
        ("6", (4, 6), (8, 12)),
        ("7", (6, 8), (4, 12)),
        ("8", (0, 10), (4, 14)),
        ("9", (6, 10), (12, 12)),
        ("a", (14, 10), (12, 14)),
        ], num_trials=args.num_trials, alg=args.alg)


    elif args.model == "ten_nets_24x24":
        main(24, 24, [
        ("1", (6, 0), (0, 6)),
        ("2", (9, 0), (6, 3)),
        ("3", (15, 0), (21, 6)),
        ("4", (18, 3), (15, 15)),
        ("5", (15, 12), (3, 15)),
        ("6", (6, 9), (12, 18)),
        ("7", (9, 12), (6, 18)),
        ("8", (0, 15), (6, 21)),
        ("9", (9, 15), (18, 18)),
        ("a", (21, 15), (18, 21))
        ], num_trials=args.num_trials, alg=args.alg)

    elif args.model == "river_8x8":
        main(8, 8, [
        ("0", (7, 0), (0, 7)),
        ("1", (7, 1), (1, 7)),
        ("2", (7, 2), (2, 7)),
        ("3", (7, 3), (3, 7)),
        ("4", (7, 4), (4, 7)),
        ("5", (7, 5), (5, 7)),
        ("6", (7, 6), (6, 7)),
        ], num_trials=args.num_trials, alg=args.alg)

    else:
        assert False, f"Unknown model: {args.model}"
