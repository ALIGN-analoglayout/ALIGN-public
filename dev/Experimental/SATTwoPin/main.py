from tally.tally import *

class Grid:
    def __init__(self, n, m, nets):
        self.s = Tally()
        self.n, self.m, self.nets = n, m, nets

        # n = 4, m = 3
        #
        #   +------+------+    0
        #   |      |      |
        #   |      |      | 0
        #   |      |      |
        #   +------+------+    1
        #   |      |      |
        #   |      |      | 1
        #   |      |      |
        #   +------+------+    2
        #   |      |      |
        #   |      |      | 2
        #   |      |      |
        #   +------+------+    3
        #      0      1
        #   0      1      2

        self.h_rasters = {}
        self.v_rasters = {}
        for net in nets:
            self.h_rasters[net] = [ [ self.s.add_var() for j in range(m-1)] for i in range(n)]
            self.v_rasters[net] = [ [ self.s.add_var() for j in range(m)] for i in range(n-1)]

        self.tallys = {}



    def gen_route_constraints(self, net, src, tgt):
        
        self.tallys[net] = []

        for i in range(self.n):
            row = []
            for j in range(self.m):
                h_edges = []
                for jj in [j-1, j]:
                    if 0 <= jj < self.m-1:
                        h_edges.append(self.h_rasters[net][i][jj])
                v_edges = []
                for ii in [i-1, i]:
                    if 0 <= ii < self.n-1:
                        v_edges.append(self.v_rasters[net][ii][j])

                if len(h_edges+v_edges) > 2:

                    tmp = [self.s.add_var() for _ in range(3)]
                    row.append(tmp)

                    self.s.emit_tally(h_edges+v_edges, tmp)

                    # tmp[0] means count > 0
                    # tmp[1] means count > 1
                    # tmp[2] means count > 2

                    if (i,j) == src or (i,j) == tgt:
                        self.s.emit_never(tmp[1])
                        self.s.emit_always(tmp[0])
                    else:
                        # we want count <= 0 or count > 1 and count <= 2
                        self.s.add_clause([-tmp[0], -tmp[2]])
                        self.s.add_clause([-tmp[0], tmp[1]])

                else:
                    # something is broken in emit_tally if len(out) > len(inp)

                    assert len(h_edges+v_edges) == 2

                    tmp = [self.s.add_var() for _ in range(2)]
                    row.append(tmp)

                    self.s.emit_tally(h_edges+v_edges, tmp)

                    # tmp[0] means count > 0
                    # tmp[1] means count > 1

                    if (i,j) == src or (i,j) == tgt:
                        self.s.emit_never(tmp[1])
                        self.s.emit_always(tmp[0])
                    else:
                        # we want count <= 0 or count > 1
                        self.s.add_clause([-tmp[0], tmp[1]])

            self.tallys[net].append(row)


    def gen_overlap_constraints(self):
        for i in range(self.n):
            for j in range(self.m):
                self.s.emit_at_most_one([self.tallys[net][i][j][0] for net in self.nets])


    def show(self):
        def h_edge_on( i, j):
            lst = []
            for net in self.nets:
                if 0 <= i < self.n and 0 <= j < self.m-1 and self.s.h[self.h_rasters[net][i][j]]:
                    lst.append(net)
            return lst

        def v_edge_on( i, j):
            lst = []
            for net in self.nets:
                if 0 <= i < self.n-1 and 0 <= j < self.m and self.s.h[self.v_rasters[net][i][j]]:
                    lst.append(net)
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

def main(n, m, problem):

    g = Grid(n, m, [net for net, _, _ in problem])

    for net, src, tgt in problem:
        g.gen_route_constraints( net, src, tgt)

    g.gen_overlap_constraints()

    g.s.solve()

    assert g.s.state == 'SAT'

    print("="*(m*6-5))
    g.show()
    print("="*(m*6-5))

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
