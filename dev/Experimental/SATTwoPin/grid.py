from tally.tally import *
import render

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

        render.show(self.n, self.m, h_edge_on, v_edge_on)



