
class AStar:
    def __init__(self, n, m):
        self.n, self.m = n, m


    def bfs(self, nm, src, tgt):
        print( nm, src, tgt)

        reached = {}

        frontier = { src }

        found = False
        count = 0
        while frontier:
            new_frontier = set()
            for i, j in frontier:
                for ii, jj in [(i-1,j), (i+1,j), (i,j-1), (i, j+1)]:
                    if 0 <= ii < self.n and 0 <= jj < self.m:
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
                    if 0 <= ii < self.n and 0 <= jj < self.m:
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


            print(''.join(s))


def main(n, m, lst):
    a = AStar(n, m)
            
    for nm, src, tgt in lst:
        a.bfs( nm, src, tgt)

if __name__ == "__main__":
    main(10, 10, [("a", (3,2), (7,6)), ("b", (6,4), (2,8))])

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
        ("a", (7, 5), (6, 7))
        ])


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
