from tally.tally import Tally, VarMgr, BitVec

def test_A0():
    s = Tally()
    mgr = VarMgr(s)

    n = 19

    def build_permutation(n):
        perm = []
        for i in range(n):
            perm.append(mgr.add_var(BitVec(s, f'a{i}', n)))
            s.emit_exactly_one(perm[-1].vars)

        for j in range(n):
            lst = []
            for i, a in enumerate(perm):
                lst.append(a.vars[j])
            s.emit_exactly_one(lst)
        return perm

    pos = build_permutation(n)
    neg = build_permutation(n)

    def ordering_constraint(n, a_u, a_v):
        for i in range(n):
            # a_u[i] => (a_v[i+1] or a_v[i+2] or ... or a_v[n-1])
            # not a_u[i] or a_v[i+1] or a_v[i+2] or ... or a_v[n-1]
            lst = [-a_u.var(i)]
            for j in range(i+1,n):
                lst.append(a_v.var(j))
            s.add_clause(lst)

    ordering_constraint(n, pos[15], pos[6])
    ordering_constraint(n, neg[15], neg[6])

    ordering_constraint(n, pos[18], pos[0])
    ordering_constraint(n, neg[0], neg[18])

    s.solve()
    assert s.state == 'SAT'

    def get_index_of_true(a):
        for i, x in enumerate(a.val()):
            if x == '1':
                return i
            else:
                assert x == '0'
        assert False

    print()
    for i, a in enumerate(pos):
        print( f'{i:2d} {get_index_of_true(a)}')
        #print( f'{i:2d} {a.val()}')
    print('====')
    for i, a in enumerate(neg):
        #print( f'{i:2d} {a.val()}')
        print( f'{i:2d} {get_index_of_true(a)}')
