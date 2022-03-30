import pytest
from tally.tally import Tally, VarMgr, BitVec
from itertools import combinations

class SeqPair:

    def __init__(self, n):
        self.n = n
        self.s = Tally()
        self.mgr = VarMgr(self.s)

        self.pos = self.build_permutation()
        self.neg = self.build_permutation()


    def build_permutation(self):
        perm = []
        for i in range(self.n):
            perm.append(self.mgr.add_var(BitVec(self.s, f'a{i}', self.n)))
            self.s.emit_exactly_one(perm[-1].vars)

        for j in range(self.n):
            lst = []
            for i, a in enumerate(perm):
                lst.append(a.vars[j])
            self.s.emit_exactly_one(lst)
        return perm

    def ordering_constraint(self, a_u, a_v):
        for i in range(self.n):
            # a_u[i] => (a_v[i+1] or a_v[i+2] or ... or a_v[n-1])
            # not a_u[i] or a_v[i+1] or a_v[i+2] or ... or a_v[n-1]
            lst = [-a_u.var(i)]
            for j in range(i+1,self.n):
                lst.append(a_v.var(j))
            self.s.add_clause(lst)

    def ordering_expr(self, a_u, a_v):
        z = self.s.add_var()

        ors = []
        for i in range(self.n):
            # a_u[i] => (a_v[i+1] or a_v[i+2] or ... or a_v[n-1])
            # not a_u[i] or a_v[i+1] or a_v[i+2] or ... or a_v[n-1]
            lst = [-a_u.var(i)]
            for j in range(i+1,self.n):
                lst.append(a_v.var(j))

            ors.append(self.s.add_var())
            self.s.emit_or(lst, ors[-1])

        self.s.emit_and(ors, z)
        return z

    @staticmethod
    def print_matrix(perm):
        for i, a in enumerate(perm):
            print( f'{i:2d} {a.val()}')


    @staticmethod
    def perm2vec(perm):
        n = len(perm)
        def get_index_of_true(i):
            for j in range(n):
                if perm[j].val(i):
                    return j
            assert False

        return [get_index_of_true(i) for i in range(n)]


    def prnt(self):
        self.print_matrix(self.pos)
        print('====')
        self.print_matrix(self.neg)
        print('====')
        print(self.perm2vec(self.pos))
        print(self.perm2vec(self.neg))

    def order_expr(self, u, v, axis='H'):
        assert axis == 'H' or axis == 'V'
        z = self.s.add_var()
        l_pos = self.ordering_expr(self.pos[u], self.pos[v])
        if axis == 'H':
            l_neg = self.ordering_expr(self.neg[u], self.neg[v])
        else:
            l_neg = self.ordering_expr(self.neg[v], self.neg[u])
        self.s.emit_and([l_pos, l_neg], z)
        return z

    def order_alt(self, u, v, axis='H'):
        assert axis == 'H' or axis == 'V'
        self.ordering_constraint(self.pos[u], self.pos[v])
        if axis == 'H':
            self.ordering_constraint(self.neg[u], self.neg[v])
        else:
            self.ordering_constraint(self.neg[v], self.neg[u])

    @staticmethod
    def other_axis(axis):
        assert axis == 'H' or axis == 'V'
        if axis == 'H':
            return 'V'
        else:
            return 'H'

    def order(self, u, v, axis='H'):
        self.s.emit_always(self.order_expr(u, v, axis))

    def align(self, u, v, axis='H'):
        # Either of these will work
        # 1) u -> v or v -> u are axis ordered
        self.s.add_clause([self.order_expr(u, v, axis), self.order_expr(v, u, axis)])
        # 2) neither u-> v nor v -> u are other_axis ordered
        #self.s.emit_never(self.order_expr(u,v, self.other_axis(axis)))
        #self.s.emit_never(self.order_expr(v,u, self.other_axis(axis)))

    def gen_assumptions(self, pvec, nvec):
        return [self.pos[x].var(i) for i, x in enumerate(pvec)] + [self.neg[x].var(i) for i, x in enumerate(nvec)]

    def abut(self, u, v, axis='H'):
        def abut_aux(u, v):
            uv_order_expr = self.order_expr(u, v, axis)

            for i in range(self.n):
                if i in [u, v]:
                    continue
                ui_order_expr = self.order_expr(u, i, axis)
                iv_order_expr = self.order_expr(i, v, axis)

                # bad if uv_order_expr and ui_order_expr and iv_order_expr
                # ok if one of the three is false
                self.s.add_clause([-uv_order_expr, -ui_order_expr, -iv_order_expr])

        abut_aux(u, v)
        abut_aux(v, u)

    def align_array(self, a, axis='H'):
        assert a
        u = a[0]
        for v in a[1:]:
            self.align(u, v, axis)

    def order_array(self, a, axis='H', abut=False):
        assert a
        for u, v in zip(a[:-1], a[1:]):
            self.order(u, v, axis)
            if abut:
                self.abut(u, v, axis)

    def symmetric(self, lst_of_lst, axis='V'):
        # default is a vertical line of symmetry
        singles = [lst for lst in lst_of_lst if len(lst) == 1]
        pairs = [lst for lst in lst_of_lst if len(lst) == 2]
        assert len(singles) + len(pairs) == len(lst_of_lst)

        print(singles, pairs)

        if len(singles) > 1:
            self.align_array([lst[0] for lst in singles], axis=axis)

        for u, v in pairs:
            self.order(u, v, axis=SeqPair.other_axis(axis))

        def symmetric_pair( pair0, pair1):
            u0, v0 = pair0
            u1, v1 = pair1

            # u0   u1  ccc   v1 v0
            # u1   u0  ccc   v0 v1

            u0u1_order = self.order_expr(u0, u1)
            self.s.add_clause([-u0u1_order,self.order_expr(u1, v1)])
            self.s.add_clause([-u0u1_order,self.order_expr(v1, v0)])

            u1u0_order = self.order_expr(u1, u0)
            self.s.add_clause([-u1u0_order,self.order_expr(u0, v0)])
            self.s.add_clause([-u1u0_order,self.order_expr(v0, v1)])


        for pair0, pair1 in combinations(pairs, 2):
            symmetric_pair(pair0, pair1)



def test_A0():
    n = 19
    sp = SeqPair(n)
    sp.order(15, 6, 'H')
    sp.order(18, 0, 'V')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

def test_order_h():
    sp = SeqPair(4)
    sp.order(3,2,'H')
    sp.order(2,1,'H')
    sp.order(1,0,'H')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    assert SeqPair.perm2vec(sp.pos) == [3,2,1,0]
    assert SeqPair.perm2vec(sp.neg) == [3,2,1,0]

def test_order_array_h():
    sp = SeqPair(4)
    sp.order_array([3,2,1,0],'H')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    assert SeqPair.perm2vec(sp.pos) == [3,2,1,0]
    assert SeqPair.perm2vec(sp.neg) == [3,2,1,0]

def test_order_v():
    sp = SeqPair(4)
    sp.order(3,2,'V')
    sp.order(2,1,'V')
    sp.order(1,0,'V')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    assert SeqPair.perm2vec(sp.pos) == [3,2,1,0]
    assert SeqPair.perm2vec(sp.neg) == [0,1,2,3]

def test_order_array_v():
    sp = SeqPair(4)
    sp.order_array([3,2,1,0],'V')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    assert SeqPair.perm2vec(sp.pos) == [3,2,1,0]
    assert SeqPair.perm2vec(sp.neg) == [0,1,2,3]

def test_order_bad_axis():
    sp = SeqPair(4)
    with pytest.raises(AssertionError) as exc:
        sp.order(3,2,'G')

def test_align_h_pass():
    sp = SeqPair(2)
    sp.align(0,1,'H')

    sp.s.solve(assumptions=sp.gen_assumptions([0,1],[0,1]))
    assert sp.s.state == 'SAT'

    sp.s.solve(assumptions=sp.gen_assumptions([0,1],[1,0]))
    assert sp.s.state == 'UNSAT'

    sp.s.solve(assumptions=sp.gen_assumptions([1,0],[1,0]))
    assert sp.s.state == 'SAT'

    sp.s.solve(assumptions=sp.gen_assumptions([1,0],[0,1]))
    assert sp.s.state == 'UNSAT'




def test_align_h_fail():
    sp = SeqPair(2)
    sp.order(0,1,'H')
    sp.align(0,1,'V')

    sp.s.solve()
    assert sp.s.state == 'UNSAT'

def test_abut_h_pass0():
    sp = SeqPair(3)
    sp.align(0,2,'H')
    sp.abut(0,2,'H')

    sp.order(0,2,'H')
    sp.order(2,1,'H')

    sp.s.solve()
    assert sp.s.state == 'SAT'

    assert SeqPair.perm2vec(sp.pos) == [0,2,1]
    assert SeqPair.perm2vec(sp.neg) == [0,2,1]

def test_assumptions():
    sp = SeqPair(3)
    sp.s.solve(assumptions=sp.gen_assumptions([2,0,1], [2,0,1]))
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    assert SeqPair.perm2vec(sp.pos) == [2,0,1]
    assert SeqPair.perm2vec(sp.neg) == [2,0,1]



def test_abut_h_pass1():
    sp = SeqPair(3)
    sp.align(0,2,'H')
    sp.abut(0,2,'H')

    sp.order(2,0,'H')
    sp.order(0,1,'H')

    sp.s.solve(assumptions=sp.gen_assumptions([2,0,1], [2,0,1]))
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()


    assert SeqPair.perm2vec(sp.pos) == [2,0,1]
    assert SeqPair.perm2vec(sp.neg) == [2,0,1]


def test_abut_h_fail():
    sp = SeqPair(3)
    sp.align(0,2,'H')
    sp.abut(0,2,'H')

    sp.order(0,1,'H')
    sp.order(1,2,'H')

    sp.s.solve()
    assert sp.s.state == 'UNSAT'

def test_soner():

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs":
            [["a", "b"], ["c", "d"], ["e"], ["f"], ["g", "h"], ["m", "n"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["f", "a", "c", "g", "m", "e"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "d"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["g", "h"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["m", "n"]}
    ]

    instances_s = "abcdefghmn"
    pos_s, neg_s = "fabcdghmen", "emgcabdfhn"

    m = {c: i for i,c in enumerate(instances_s)}
    
    invm = list(instances_s)

    axis_tbl = {"top_to_bottom": "V", "left_to_right": "H"}

    sp = SeqPair(len(m))

    for constraint in constraints:
        if constraint['constraint'] == "Order":
            axis = axis_tbl[constraint['direction']]
            sp.order_array( [m[iname] for iname in constraint['instances']], axis=axis, abut=True)

        if constraint['constraint'] == "SymmetricBlocks":
            axis = constraint['direction']
            sp.symmetric( [ [m[iname] for iname in lst] for lst in constraint['pairs']], axis=axis)

    #assump = sp.gen_assumptions([m[c] for c in "fabcdghmen"], [m[c] for c in "emgcabdfhn"])
    assump = None

    sp.s.solve(assumptions=assump)
    assert sp.s.state == 'SAT'

    print( ''.join(invm[x] for x in SeqPair.perm2vec(sp.pos)),  ''.join(invm[x] for x in SeqPair.perm2vec(sp.neg)))
