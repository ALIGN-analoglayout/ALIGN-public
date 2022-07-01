from collections import defaultdict


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

        print(h_edges)
        print(v_edges)

        def h_edge_on( i, j):
            lst = set()
            if 0 <= i < self.n and 0 <= j < self.m-1:
                nets = h_edges[((i,j),(i,j+1))]
                lst.update(nets)
            #print('h_edge_on', i, j, lst)
            return lst

        def v_edge_on( i, j):
            lst = set()
            if 0 <= i < self.n-1 and 0 <= j < self.m:
                nets = v_edges[((i,j),(i+1,j))]
                lst.update(nets)
            #print('v_edge_on', i, j, lst)
            return lst

        for i in range(self.n):
            for ii in range(4):
                if i == self.n-1 and ii > 0:
                    continue
                for j in range(self.m):
                    for jj in range(6):
                        if j == self.m-1 and jj > 0:
                            continue
                        ch = ' '
                        if ii == 0 and jj == 0:
                            s = set()
                            s.update(h_edge_on(i, j))
                            s.update(h_edge_on(i, j-1))
                            s.update(v_edge_on(i, j))
                            s.update(v_edge_on(i-1, j))
                            assert len(s) <= 1
                            if len(s) == 1:
                                ch = list(s)[0]

                        elif ii == 0 and jj > 0:
                            s = set()
                            s.update(h_edge_on(i, j))
                            assert len(s) <= 1
                            if len(s) == 1:
                                ch = list(s)[0]

                        elif ii > 0 and jj == 0:
                            s = set()
                            s.update(v_edge_on(i, j))
                            assert len(s) <= 1
                            if len(s) == 1:
                                ch = list(s)[0]

                        print(ch, end='')
                print('')


    def bfs(self, nm, src, tgt, obstacles=None):

        if obstacles is None:
            obstacles_s = set()
        else:
            obstacles_s = obstacles


        reached = {}

        frontier = { src }

        found = False
        count = 0
        while frontier:
            new_frontier = set()
            for i, j in frontier:
                for ii, jj in [(i-1,j), (i+1,j), (i,j-1), (i, j+1)]:
                    if 0 <= ii < self.n and 0 <= jj < self.m and (ii, jj) not in obstacles_s:
                        new_frontier.add((ii, jj))
                        if (ii, jj) == tgt:
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
                i, j = u
                for ii, jj in [(i-1,j), (i+1,j), (i,j-1), (i, j+1)]:
                    if 0 <= ii < self.n and 0 <= jj < self.m and (ii, jj) not in obstacles_s:
                        v = ii, jj
                        if v in reached:
                            if reached[v]+1 == reached[u]:
                                u = v
                                path.append(u)
                                break
                else:
                    assert False


            path = list(reversed(path))
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


            return ''.join(s), path
        else:
            return None, None

def main(n, m, lst, obstacles=None):
    print("="*80)

    a = Lee(n, m)

    obstacles = set()

    for _, src, tgt in lst:
        obstacles.add(src)
        obstacles.add(tgt)

    for nm, src, tgt in lst:
        obstacles.remove(src)
        obstacles.remove(tgt)

        path_s, path_l = a.bfs( nm, src, tgt, obstacles=obstacles)

        if path_l is None:
            obstacles.add(src)
            obstacles.add(tgt)
        else:
            obstacles.update(path_l)

            a.add_path(nm, path_l)

        print(nm, src, tgt, path_s)

    a.show()

if __name__ == "__main__":
    if True:
        main(10, 10, [("a", (3,2), (7,6)), ("b", (6,4), (2,8))], {(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3),(8,3),(9,3)})

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

    if True:
        main(8, 8, [

        ("2", (3, 0), (2, 1)),

        ("4", (6, 1), (5, 5)),
        ("5", (5, 4), (1, 5)),
        ("6", (2, 3), (4, 6)),
        ("7", (3, 4), (2, 6)),
        ("8", (0, 5), (2, 7)),
        ("9", (3, 5), (6, 6)),
        ("a", (7, 5), (6, 7)),
        ("3", (5, 0), (7, 2)),
        ("1", (2, 0), (0, 2)),
        ])


    if True:
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
        ])
