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

        self.cache = {}

        self.specified_alignments = set()

        self.semantic_run = False


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

        k = (u,v,axis)
        if k in self.cache:
            return self.cache[k]

        assert axis == 'H' or axis == 'V'
        z = self.s.add_var()
        l_pos = self.ordering_expr(self.pos[u], self.pos[v])
        if axis == 'H':
            l_neg = self.ordering_expr(self.neg[u], self.neg[v])
        else:
            l_neg = self.ordering_expr(self.neg[v], self.neg[u])
        self.s.emit_and([l_pos, l_neg], z)

        self.cache[k] = z

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
        return {'H': 'V', 'V': 'H'}[axis]

    def order(self, u, v, axis='H'):
        self.s.emit_always(self.order_expr(u, v, axis))

    def align(self, u, v, axis='H'):
        self.specified_alignments.add((u,v,axis))

    def align_add_constraint(self, u, v, axis='H'):
        # Either of these will work
        # 1) u -> v or v -> u are axis ordered
        self.s.add_clause([self.order_expr(u, v, axis), self.order_expr(v, u, axis)])
        # 2) neither u-> v nor v -> u are other_axis ordered
        #self.s.emit_never(self.order_expr(u,v, self.other_axis(axis)))
        #self.s.emit_never(self.order_expr(v,u, self.other_axis(axis)))


    def semantic(self):
        for (u,v,a) in self.specified_alignments:
            self.align_add_constraint(u,v,axis=a)
        self.semantic_run = True

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

    def symmetric_pairs_ordered(self, lst_of_lst, axis='V'):
        # default is a vertical line of symmetry
        singles = [lst[0] for lst in lst_of_lst if len(lst) == 1]
        pairs = [lst for lst in lst_of_lst if len(lst) == 2]
        assert len(singles) + len(pairs) == len(lst_of_lst)

        oa = SeqPair.other_axis(axis)

        if len(singles) > 1:
            self.align_array(singles, axis=axis)

        for u, v in pairs:
            # force u is (to the left of)/(on top of) v
            self.order(u, v, axis=oa)
            # if one of a pair is ordered with a single, then the other needs to b reverse ordered
            for x in singles:
                self.s.emit_iff(self.order_expr(u,x,axis=oa), self.order_expr(x,v,axis=oa))

        for (u0, v0), (u1, v1) in combinations(pairs, 2):
            # u0   u1  ccc   v1 v0
            # (u0<u1) => u1 < v1 and v1 < v0
            self.s.emit_implies(self.order_expr(u0, u1, axis=oa), self.order_expr(u1, v1, axis=oa))
            self.s.emit_implies(self.order_expr(u0, u1, axis=oa), self.order_expr(v1, v0, axis=oa))

            # u1   u0  ccc   v0 v1
            # (u1<u0) => u0 < v0 and v0 < v1
            self.s.emit_implies(self.order_expr(u1, u0, axis=oa), self.order_expr(u0, v0, axis=oa))
            self.s.emit_implies(self.order_expr(u1, u0, axis=oa), self.order_expr(v0, v1, axis=oa))

    def symmetric(self, lst_of_lst, axis='V'):
        # default is a vertical line of symmetry
        singles = [lst[0] for lst in lst_of_lst if len(lst) == 1]
        pairs = [lst for lst in lst_of_lst if len(lst) == 2]
        assert len(singles) + len(pairs) == len(lst_of_lst)

        oa = SeqPair.other_axis(axis)

        if len(singles) > 1:
            self.align_array(singles, axis=axis)

        def aux0(l,u,x,v):
            self.s.add_clause([-l, -self.order_expr(u,x,axis=oa), self.order_expr(x,v,axis=oa)])
            self.s.add_clause([-l, -self.order_expr(x,v,axis=oa), self.order_expr(u,x,axis=oa)])

        for u, v in pairs:
            self.align(u,v,axis=oa)

            # if one of a pair is ordered with a single, then the other needs to b reverse ordered
            p = self.order_expr(u,v,axis=oa)
            n = self.order_expr(v,u,axis=oa)

            for x in singles:
                aux0(p,u,x,v)
                aux0(n,v,x,u)


        def aux1(l0,l1,u0,v0,u1,v1):
            self.s.add_clause([-l0,-l1,-self.order_expr(u0, u1, axis=oa), self.order_expr(u1, v1, axis=oa)])
            self.s.add_clause([-l0,-l1,-self.order_expr(u0, u1, axis=oa), self.order_expr(v1, v0, axis=oa)])
            self.s.add_clause([-l0,-l1,-self.order_expr(u1, u0, axis=oa), self.order_expr(u0, v0, axis=oa)])
            self.s.add_clause([-l0,-l1,-self.order_expr(u1, u0, axis=oa), self.order_expr(v0, v1, axis=oa)])

        for (u0, v0), (u1, v1) in combinations(pairs, 2):
            p0 = self.order_expr(u0,v0,axis=oa)
            n0 = self.order_expr(v0,u0,axis=oa)
            p1 = self.order_expr(u1,v1,axis=oa)
            n1 = self.order_expr(v1,u1,axis=oa)

            aux1(p0,p1,u0,v0,u1,v1)
            aux1(n0,p1,v0,u0,u1,v1)
            aux1(p0,n1,u0,v0,v1,u1)
            aux1(n0,n1,v0,u0,v1,u1)


    def solve_and_check(self, expected_status='SAT'):
        if not self.semantic_run:
            self.semantic()

        self.s.solve()
        assert self.s.state == expected_status
        if expected_status == 'SAT':
            print()
            self.prnt()

    def gen_solutions(self, max_solutions=100):
        if not self.semantic_run:
            self.semantic()

        # Only get to run this once "Destroys the model"
        control = self.s.add_var()
        for i in range(max_solutions):
            self.s.solve(assumptions=[control])
            #print(self.s.solver.accum_stats())
            if self.s.state != 'SAT':
                break
            p_res, n_res = SeqPair.perm2vec(self.pos), SeqPair.perm2vec(self.neg)
            
            yield tuple(p_res), tuple(n_res)

            self.s.add_clause([-control]+[-x for x in self.gen_assumptions(p_res, n_res)])


def test_order_h():
    sp = SeqPair(4)
    sp.order(3,2,'H')
    sp.order(2,1,'H')
    sp.order(1,0,'H')

    assert {((3,2,1,0),(3,2,1,0))} == set(sp.gen_solutions(max_solutions=100))

def test_order_array_h():
    sp = SeqPair(4)
    sp.order_array([3,2,1,0],'H')

    assert {((3,2,1,0),(3,2,1,0))} == set(sp.gen_solutions(max_solutions=100))


def test_order_v():
    sp = SeqPair(4)
    sp.order(3,2,'V')
    sp.order(2,1,'V')
    sp.order(1,0,'V')

    assert {((3,2,1,0),(0,1,2,3))} == set(sp.gen_solutions(max_solutions=100))


def test_order_array_v():
    sp = SeqPair(4)
    sp.order_array([3,2,1,0],'V')

    assert {((3,2,1,0),(0,1,2,3))} == set(sp.gen_solutions(max_solutions=100))


def test_order_bad_axis():
    sp = SeqPair(4)
    with pytest.raises(AssertionError) as exc:
        sp.order(3,2,'G')


def test_align_h_pass():
    sp = SeqPair(2)
    sp.align(0,1,'H')

    assert {((0,1),(0,1)), ((1,0),(1,0))} == set(sp.gen_solutions(max_solutions=100))


def test_align_h_fail():
    sp = SeqPair(2)
    sp.order(0,1,'H')
    sp.align(0,1,'V')

    assert set() == set(sp.gen_solutions(max_solutions=100))

def test_align_transitive_fail():
    sp = SeqPair(3)

    #  (0, 2, 1), (2, 0, 1) and 3 others
    #
    #  0 < 1
    #  ^
    #  2 < 1
    #
    # This only works if the 0,1 is an align top and 1,2 is an align bot and the size of block 1 is no less than the sum of block 0 and block 2

    sp.align(0,1,'H')
    sp.align(1,2,'H')
    sp.align(0,2,'H')
    sp.align(0,2,'V')

    assert set() == set(sp.gen_solutions(max_solutions=100))

def test_align_order_transitive_fail():
    sp = SeqPair(3)

    #  (0, 2, 1), (2, 0, 1) and 3 others
    #
    #  0 < 1
    #  ^
    #  2 < 1
    #
    # This only works if the 0,1 is an align top and 1,2 is an align bot and the size of block 1 is no less than the sum of block 0 and block 2

    sp.order(0,1,'H')
    sp.order(2,1,'H')
    sp.align(0,2,'V')

    assert set() == set(sp.gen_solutions(max_solutions=100))

def test_abut_h_pass0():
    sp = SeqPair(3)
    sp.align(0,2,'H')
    sp.abut(0,2,'H')

    sp.order(0,2,'H')
    sp.order(2,1,'H')

    assert {((0,2,1),(0,2,1))} == set(sp.gen_solutions(max_solutions=100))


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

def test_symmetric_2():
    sp = SeqPair(2)
    sp.symmetric([[0,1]], 'V')
    sp.align_array([0,1], 'H')

    assert {((0,1),(0,1)),((1,0),(1,0))} == set(sp.gen_solutions(max_solutions=100))

def test_symmetric_3():
    sp = SeqPair(3)
    sp.symmetric([[0], [1,2]], 'V')

    sp.s.dump_cnf("symmetric_3.cnf")

    assert 6 == len(set(sp.gen_solutions(max_solutions=100)))

def test_symmetric_4():
    sp = SeqPair(4)
    sp.symmetric([[0,1], [2,3]], 'V')

    sp.s.dump_cnf("symmetric_4.cnf")

    assert 80 == len(set(sp.gen_solutions(max_solutions=1000)))

def satisfy_constraints(constraints, pos_solution=None, neg_solution=None, single_character=False, max_solutions=1):
    instances_s = set()

    for constraint in constraints:
        if constraint['constraint'] == 'Order' or constraint['constraint'] == "Align":
            for iname in constraint['instances']:
                instances_s.add(iname)
        elif constraint['constraint'] == 'SymmetricBlocks':
            for lst in constraint['pairs']:
                for iname in lst:
                    instances_s.add(iname)                    
        else:
            assert False, constraint

    m = {c: i for i,c in enumerate(instances_s)}
    
    invm = list(instances_s)

    axis_tbl = {"top_to_bottom": "V", "left_to_right": "H", "h_bottom": "H", "v_left": "V"}

    sp = SeqPair(len(m))

    for constraint in constraints:
        if constraint['constraint'] == "Order":
            axis = axis_tbl[constraint['direction']]
            abut = constraint.get('abut', False)
            sp.order_array( [m[iname] for iname in constraint['instances']], axis=axis, abut=abut)

        elif constraint['constraint'] == "SymmetricBlocks":
            axis = constraint['direction']
            sp.symmetric( [ [m[iname] for iname in lst] for lst in constraint['pairs']], axis=axis)

        elif constraint['constraint'] == "Align":
            axis = axis_tbl[constraint['direction']]
            sp.align_array([m[iname] for iname in constraint['instances']], axis=axis)

        else:
            assert False, constraint

    assump = None
    if pos_solution is not None and neg_solution is not None:
        assert len(pos_solution) == len(m) and len(neg_solution) == len(m)
        assump = sp.gen_assumptions([m[c] for c in pos_solution], [m[c] for c in neg_solution])

    sp.s.solve(assumptions=assump)
    assert sp.s.state == 'SAT'

    print()
    sp.prnt()

    p_res, n_res = [invm[x] for x in SeqPair.perm2vec(sp.pos)],  [invm[x] for x in SeqPair.perm2vec(sp.neg)]

    if single_character:
        print(''.join(p_res), ''.join(n_res))
    else:
        print(p_res, n_res)
    

    for i, (p_res, n_res) in enumerate(sp.gen_solutions(max_solutions)):
        p_res_s, n_res_s = [invm[x] for x in p_res], [invm[x] for x in n_res]
        if single_character:
            print(f'Solution: {i:4d}', ''.join(p_res_s), ''.join(n_res_s))
        else:
            print(f'Solution: {i:4d}', p_res_s, n_res_s)

    return sp


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

    #pos_s, neg_s = "fabcdghmen", "emgcabdfhn"
    pos_s, neg_s = "fabcdghmne", "emgcabdhnf"
    pos_s, neg_s = None, None

    #
    #                       f
    #                  a         b
    #                  c         d
    #                  g    |    h
    #                  m         n
    #                       e 

    satisfy_constraints(constraints, pos_s, neg_s, single_character=True, max_solutions=100)



def test_soner2():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs":
            [["a", "b"], ["c", "d"], ["e"], ["f"], ["g", "h"], ["m", "n"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["f", "a", "c", "g", "m", "e"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "d"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["g", "h"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["m", "n"]},
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b", "o", "p"]},
        {"constraint": "Align", "direction": "v_left", "instances": ["c", "g", "r"]}
    ]



    #                       f
    #      o    p      a         b
    #                  c         d
    #                  g    |    h
    #                  m         n
    #                       e 
    #                  r


    #pos_s, neg_s = "fopabcdghmenr", "emnoprgcabdfh"
    pos_s, neg_s = "fopabcdghmner", "remnghcdopabf"
    pos_s, neg_s = None, None

    sp = satisfy_constraints(constraints, pos_s, neg_s, single_character=True, max_solutions=100)

    


def test_soner_big():
    constraints = [
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPTAIL']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPPBIAS']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PULLUP_ENB']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PBIAS_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES0', 'X_XDECAP_NZ3']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES1', 'X_XDECAP_NZ3']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XPTAIL', 'X_XP2', 'X_XPPBIAS', 'X_XSW_PULLUP_ENB', 'X_XSW_PBIAS_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVP1', 'X_XINVP2', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XSW_PULLDN_EN', 'X_CM_XNLDL_XNLDR', 'X_XSW_PULLDN_EN1', 'X_XN2', 'X_XINVN1', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XNRES0', 'X_XNRES1']},
        {'constraint': 'SymmetricBlocks', 'direction': 'V', 'pairs': [['X_XPTAIL'], ['X_DP_XPINP_XPINN'], ['X_CM_XNLDL_XNLDR'], ['X_XSW_PULLDN_EN', 'X_XSW_PULLDN_EN1']]},
    ]


    #pos_s, neg_s = ['X_XDECAP_P', 'X_XPTAIL', 'X_XP2', 'X_XPPBIAS', 'X_XSW_PULLUP_ENB', 'X_XSW_PBIAS_EN', 'X_DP_XPINP_XPINN', 'X_XINVP1', 'X_XINVP2', 'X_XMP_TIE_HI', 'X_XSW_PULLDN_EN', 'X_CM_XNLDL_XNLDR', 'X_XSW_PULLDN_EN1', 'X_XN2', 'X_XINVN1', 'X_XINVN2', 'X_XNRES0', 'X_XNRES1', 'X_XDECAP_NZ3'], ['X_XDECAP_NZ3', 'X_XNRES0', 'X_XNRES1', 'X_XSW_PULLDN_EN', 'X_CM_XNLDL_XNLDR', 'X_XSW_PULLDN_EN1', 'X_XN2', 'X_XINVN1', 'X_XINVN2', 'X_DP_XPINP_XPINN', 'X_XINVP1', 'X_XINVP2', 'X_XMP_TIE_HI', 'X_XPTAIL', 'X_XP2', 'X_XPPBIAS', 'X_XSW_PULLUP_ENB', 'X_XSW_PBIAS_EN', 'X_XDECAP_P']

    pos_s, neg_s = None, None

    satisfy_constraints(constraints, pos_s, neg_s, max_solutions=100)

if __name__ == "__main__":
    test_soner_big()
