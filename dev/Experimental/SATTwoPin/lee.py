from collections import defaultdict, Counter
from itertools import chain
import random
import render
import argparse
import re
import json
import subprocess
import time


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

    def _astar(self, nm, src, tgt, obstacles, heuristic=(lambda v: 0)):

        def adjacent_states(u):
            i, j, k = u

            if k == 0: # vertical
                next_states = [(i-1,j,0),(i+1,j,0),(i,j,1)]

            elif k == 1: # horizontal
                next_states = [(i,j-1,1),(i,j+1,1),(i,j,0)]
            else:
                assert False

            for ii, jj, kk in next_states:
                if 0 <= ii < self.n and 0 <= jj < self.m and 0 <= kk < 2 and (ii, jj) not in obstacles:
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


    def dijkstra(self, nm, src, tgt, obstacles):
        return self._astar(nm, src, tgt, obstacles)


    def astar(self, nm, src, tgt, obstacles):
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

        return self._astar(nm, src, tgt, obstacles, heuristic=heuristic)

    def route_all(self, nets, lst, alg='astar', check=False):
        """Route the seq 'lst' which is a subset of all the nets 'nets'"""

        fn = self.astar if alg == 'astar' else self.dijkstra

        all_ok = True

        #print("="*80)

        obstacles = set()

        for _, src, tgt in nets:
            obstacles.add(src)
            obstacles.add(tgt)

        for nm, src, tgt in lst:
            obstacles.remove(src)
            obstacles.remove(tgt)

            path_l = fn( nm, src, tgt, obstacles)

            if check:
                path_l_ref = self.dijkstra( nm, src, tgt, obstacles)
                assert (path_l is None) == (path_l_ref is None)

                if path_l is not None:
                    pl, pl_ref = self.path_length(path_l), self.path_length(path_l_ref)
                    #print(f'Checking path lengths: {alg} {pl} dijkstra {pl_ref}')
                    assert pl == pl_ref

            #path_str, path_cost = (self.path2str(path_l), self.path_length(path_l)) if path_l is not None else (None, None)
            #print(nm, src, tgt, path_str, path_cost)

            if path_l is None:
                obstacles.add(src)
                obstacles.add(tgt)
                all_ok = False
            else:
                obstacles.update([tup[:2] for tup in path_l])
                self.add_path(nm, path_l)

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
        

    def is_routable(self, e, alg, check, nets):
        return self.route_all(nets, [nets[idx] for idx in e], alg=alg, check=check)


def determine_order(nets):
    counts = []

    for net0, src0, tgt0 in nets:
        bbox = min(src0[0], tgt0[0]), min(src0[1], tgt0[1]), max(src0[0], tgt0[0]), max(src0[1], tgt0[1]), 

        count = 0

        for net1, src1, tgt1 in nets:
            if net0 == net1:
                continue

            for pnt in (src1, tgt1):
                if bbox[0] < pnt[0] < bbox[2] and bbox[1] < pnt[1] < bbox[3]:
                    count += 1

        counts.append(count)

    ordering = list(sorted(zip(counts,nets)))
    print(ordering)

    return [b for _, b in ordering]

class StrongPruning:
    def __init__(self, args, n_i, n_j, nets):
        self.args = args
        self.n_i = n_i
        self.n_j = n_j
        self.nets = nets
        self.stack = ()

        self.obstructions = None


    def pop(self):
        res = self.stack[-1]
        self.stack = self.stack[:-1]
        return res

    def push(self, x):
        self.stack = self.stack + (x,)

    def check(self):
        return Lee(self.n_i, self.n_j).is_routable(self.stack, self.args.alg, self.args.check, self.nets)

    def strong_prune(self, possible):
        print(f'strong_prune: {self.disp()}')
        most_constraining_e = self.stack
        
        last = self.pop()
        self.push(last)

        for x in chain((last,), possible):
            self.pop()
            self.push(x)

            if not self.check():
                print(f'found failure: {self.disp()}')
                while True:

                    save_e = self.stack

                    if len(self.stack) > 1:
                        y = self.pop()
                        z = self.pop()
                        self.push(y)

                        ok = self.check()
                        print(f'{self.disp(save_e)} -> {self.disp()} {ok}')
                        if ok:
                            y = self.pop()
                            self.push(z)
                            self.push(y)
                            break
                    else:
                        break

                self.pop()
                most_constraining_e = self.stack

            if not self.stack:
                break

        return most_constraining_e


    def disp(self, e=None):
        ee = e
        if e is None:
            ee = self.stack

        a = [self.nets[x][0] for x in ee]

        if all(len(x) == 1 for x in a):
            return ''.join(a)
        else:
            return ','.join(a)

    def strong_pruning(self):
        n = len(self.nets)

        rnd = random.Random()
        if args.seed is not None:
            rnd.seed(args.seed)

        successes = 0
        done = False

        failed = set()

        trial = 0
        restarts = 0
        while trial + restarts < args.num_trials and not done:

            possible = set(range(n))

            self.stack = ()

            while len(self.stack) < n:
                #print(f'before {self.disp()}')

                if () in failed:
                    break


                order = [j for j in possible if self.stack + (j,) not in failed]

                if not order:
                    break

                j = rnd.choice(order)

                self.push(j)


                possible.remove(j)
                if not self.check():
                    most_constraining_e = self.strong_prune(possible)
                    print(f'marked {self.disp(most_constraining_e)} as failed')
                    failed.add(tuple(most_constraining_e))

                    self.stack = most_constraining_e[:-1]

                    print(f'Restarting with {self.disp()}')
                    e_s = set(self.stack)
                    possible = set(i for i in range(n) if i not in e_s)
                    restarts += 1
                elif len(self.stack) == n:
                    successes += 1
                    print(f'{self.disp()} succeeded on trial {trial}')
                    yield self.stack
                    if not args.dont_stop_after_first:
                        done = True

            trial += 1

        def plural(tag, value, p="s"):
            return f'{value} {tag}{p if value != 1 else ""}'

        print(f'{plural("success", successes, "es")} out of {plural("trial", trial)} and {plural("restart", restarts)}.')

        return self.stack


def main(n_i, n_j, nets, args):
    num_trials = args.num_trials
    count = 0
    histo = Counter()

    nets = [(nm, tuple(src), tuple(tgt)) for nm, src, tgt in nets]

    def route(samp):
        nonlocal count

        a = Lee(n_i, n_j)

        ok = a.route_all(samp, samp, alg=args.alg, check=args.check)
        if ok:
            count += 1
            histo[a.total_wire_length()] += 1
            subprocess.run(["clear"])
            a.show()
            print(f'Routed all {len(nets)} nets. Wire Length = {a.total_wire_length()} Dequeues: {a.sum_of_counts}')
        else:
            ...
            #print(f'Only routed {len(a.paths)} of {len(nets)} nets.')



    if args.strong_pruning:
        for e in StrongPruning(args, n_i, n_j, nets).strong_pruning():
            route([nets[idx] for idx in e])

        print(f'Successfully routed {count} of {num_trials} times.')


    elif args.order:
        samp = determine_order(nets)
        route(samp)
        if count == 1:
            print(f'Successfully routed using the ordering heuristic.')
        else:
            print(f'Routing failed when using the ordering heuristic.')
    else:
        for _ in range(num_trials):
            samp = random.sample(nets, len(nets))



            route(samp)


        print(f'Successfully routed {count} of {num_trials} times.')

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
    parser.add_argument("--seed", type=int, default=None)
    parser.add_argument("-c", "--check", action='store_true')
    parser.add_argument("-o", "--order", action='store_true')
    parser.add_argument("--strong_pruning", action='store_true')
    parser.add_argument("--dont_stop_after_first", action="store_true")
    parser.add_argument("-i", "--input_json", type=str, default=None)

    args = parser.parse_args()

    if args.seed is not None:
        random.seed(args.seed)


    if args.input_json is not None:
        with open(args.input_json, "rt") as fp:
            j = json.load(fp)
            main(**j, args=args)

        exit()


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

    p = re.compile(r'^(ten_nets|simple|synthetic|river|random)_(\d+)x(\d+)$')
    p3 = re.compile(r'^(random)_(\d+)x(\d+)_(\d+)$')

    if (m := p.match(args.model)) is not None:
        subs = m.groups()
        n_i = int(subs[1])
        n_j = int(subs[2])

        if subs[0] in ['ten_nets', 'simple']:
            assert n_i == n_j
            nets = ten_nets if subs[0] == 'ten_nets' else simple_nets
            factor = (n_i+7) // 8
            main(n_i, n_j, list(scale(nets, factor)), args)

        elif subs[0] == 'synthetic':
            nets = []
            assert n_i == 4
            assert n_j % 4 == 0

            k = n_j // 4 # number of pairs

            for i in range(k):
                nets.append( (chr(ord('a')+i), (1, 4*i+0), (3, 4*i+2)))
                nets.append( (chr(ord('A')+i), (2, 4*i+1), (0, 4*i+3)))

            main(n_i, n_j, nets, args)

        elif subs[0] == 'river':
            nets = []
            assert n_i == n_j
            nnets = n_i // 2 - 1
            for i in range(nnets):
                nets.append( (chr(ord('a')+i), (i, n_i//2-1-i), (n_i//2+i, n_i-1-i)))

            main(n_i, n_j, nets, args)

        else:
            assert False, subs

    elif (m := p3.match(args.model)) is not None:

        subs = m.groups()
        n_i = int(subs[1])
        n_j = int(subs[2])
        nnets = int(subs[3])

        if subs[0] == 'random':
            nms = 'abcedfghijklmnopqrstuvwxyzABCEDFGHIJKLMNOPQRSTUVWXYZ0123456789~!@#$%^&*()_+`-={}[]|\<>?,/'


            nets = []
            endpoints = set()

            def get_rand_point(n_i, n_j, s_i, s_j):
                while True:
                    nn_i = n_i-s_i
                    nn_j = n_j-s_j
                    i = random.randrange( 0, nn_i)
                    j = random.randrange( 0, nn_j)
                    if (i,j) not in endpoints and (i+s_i,j+s_j) not in endpoints:
                        endpoints.add((i,j))
                        endpoints.add((i+s_i,j+s_j))
                        return (i,j), (i+s_i, j+s_j)

            for k in range(nnets):
                s_i = random.randrange(1, 8 if k % 5 == 0 else 4)
                s_j = random.randrange(1, 8 if k % 5 == 0 else 4)

                nets.append( (nms[k],) + get_rand_point(n_i, n_j, s_i, s_j))

            with open("__save_nets.json", "wt") as fp:
                json.dump({'n_i': n_i, 'n_j': n_j, 'nets': nets}, fp=fp, indent=2)


            main(n_i, n_j, nets, args)
        else:
            assert False, subs

    elif args.model == "two_nets_10x10":
        main(10, 10, [("a", (3,2), (7,6)), ("b", (6,4), (2,8))], args)

    else:
        assert False, f"Unknown model: {args.model}"
