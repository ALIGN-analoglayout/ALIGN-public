from tally import tally

def check_monomorphism( g, h, pi):
    # h is a subgraph of g
    assert len(pi) is len(h.nodes)

    g_edges = { (e[0],e[1]) for e in g.edges}

    # every edge in h should "map" to an edge in g
    res = True
    for e in h.edges:
        u = pi[e[0]]
        v = pi[e[1]]
        if (u,v) not in g_edges and (v,u) not in g_edges:
            res = False

    return res

def check_subgraph_isomorphism( g, h, pi):
    # h is a subgraph of g
    assert len(pi) is len(h.nodes)

    pi_inv = { pi[i]:i for (i,p) in enumerate(pi)}
    pi_inv_domain = set(pi_inv.keys())

    print("pi_inv:", pi_inv, "pi_inv_domain:", pi_inv_domain)

    h_edges = { (e[0],e[1]) for e in h.edges}

    # every edge in h should "map" to an edge in g

    res = True
    for e in g.edges:
        if e[0] not in pi_inv_domain: continue
        if e[1] not in pi_inv_domain: continue

        uh = pi_inv[e[0]]
        vh = pi_inv[e[1]]

        if (uh,vh) not in h_edges and (vh,uh) not in h_edges:
            res = False

    return res

def sat_subgraph_monomorphism( g, h):
    # h is a subgraph g
    # each vertex in h maps to some vertex in g
    # set up two dimensional array

    s = tally.Tally()
    mgr = tally.VarMgr( s)

    lst = []
    for n in g.nodes:
        lst.append( mgr.add_var( tally.BitVec( s, str(n), len(h.nodes))))
        s.emit_at_most_one( lst[-1].vars)

    for (idx,n) in enumerate(h.nodes):
        l = []
        for bv in lst:
            l.append( bv.vars[idx])
        s.emit_exactly_one( l)

    for eh in h.edges:
        # if eh in h.edges, then map(eh) must be in g.edges
        lits = []
        for eg in g.edges:
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[0]].vars[eh[0]], lst[eg[1]].vars[eh[1]]], lits[-1])
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[1]].vars[eh[0]], lst[eg[0]].vars[eh[1]]], lits[-1])
        s.add_clause( lits)

    s.solve()

    if s.state == 'SAT':
        for bv in lst:
            print( bv.val())

        res_tbl = []

        for (idx,n) in enumerate(h.nodes):
            res = None
            for (jdx,bv) in enumerate(lst):
                if bv.val(idx):
                    res = jdx
            assert res is not None
            res_tbl.append( res)

        print( res_tbl)

        assert check_monomorphism( g, h, res_tbl)


    return s.state == 'SAT'

def sat_subgraph_isomorphism( g, h):
    # h is a subgraph g
    # each vertex in h maps to some vertex in g
    # set up two dimensional array

    s = tally.Tally()
    mgr = tally.VarMgr( s)

    lst = []
    for n in g.nodes:
        lst.append( mgr.add_var( tally.BitVec( s, str(n), len(h.nodes))))
        s.emit_at_most_one( lst[-1].vars)

    for (idx,n) in enumerate(h.nodes):
        l = []
        for bv in lst:
            l.append( bv.vars[idx])
        s.emit_exactly_one( l)

    isMapped = []
    for bv in lst:
        isMapped.append( s.add_var())
        s.emit_or( bv.vars, isMapped[-1])

    for eg in g.edges:
        lits = []
        lits.append( -isMapped[eg[0]])
        lits.append( -isMapped[eg[1]])
        for eh in h.edges:
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[0]].vars[eh[0]], lst[eg[1]].vars[eh[1]]], lits[-1])
            lits.append( s.add_var())
            s.emit_and( [ lst[eg[1]].vars[eh[0]], lst[eg[0]].vars[eh[1]]], lits[-1])
        s.add_clause( lits)

    s.solve()

    if s.state == 'SAT':
        for bv in lst:
            print( bv.val())

        res_tbl = []

        for (idx,n) in enumerate(h.nodes):
            res = None
            for (jdx,bv) in enumerate(lst):
                if bv.val(idx):
                    res = jdx
            assert res is not None
            res_tbl.append( res)

        print( res_tbl)

        assert check_subgraph_isomorphism( g, h, res_tbl)


    return s.state == 'SAT'
