from Align_primitives import main, gen_parser, get_xcells_pattern

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.rd.different_widths) == 0, uc.rd.different_widths
    assert len(uc.rd.subinsts) == get_xcells_pattern(args)[0] * args.Ycells, uc.rd.subinsts
    assert all(len(x.pins) == 4 for x in uc.rd.subinsts.values()), uc.rd.subinsts
    assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test( p, *, n, X, Y):
    b = f"{p}_n{n}_X{X}_Y{Y}"
    check_shorts( ['-p', p, '-b', b, '-n', f"{n}", '-X', f"{X}", '-Y', f"{Y}"])

def test_a0():
    build_test( 'Switch_PMOS', n=12, X=1, Y=1)
def test_a1():
    build_test( 'Switch_NMOS', n=12, X=3, Y=3)
def test_a2():
    build_test( 'DCL_NMOS',    n=12, X=2, Y=1)
def test_a3():
    build_test( 'Switch_NMOS', n=12, X=3, Y=1)
def test_a4():
    build_test( 'Switch_PMOS', n=12, X=2, Y=1)
def test_a5():
    build_test( 'CMC_PMOS_S',  n=12, X=1, Y=1)
def test_a6():
    build_test( 'DP_NMOS',     n=12, X=3, Y=3)
def test_a7():
    build_test( 'CMFB_NMOS',   n=12, X=3, Y=1)
def test_a8():
    build_test( 'CMC_PMOS',    n=12, X=2, Y=1)
def test_a9():
    build_test( 'CMC_NMOS',    n=12, X=3, Y=1)
def test_a10():
    build_test( 'SCM_NMOS',    n=12, X=1, Y=1)
def test_a11():
    build_test( 'SCM_PMOS',    n=12, X=1, Y=1)

def test_ALL():
    fins = [12, 16]
    types = ["NMOS", "PMOS"]
    pstrs = ["Switch_{}", "DCL_{}", "CM_{}", "CMFB_{}", "SCM_{}", "CMC_{}", "CMC_{}_S", "DP_{}"]
    for typ in types:
        for pstr in pstrs:
            prim = pstr.format(typ)
            for j in range(1,4):
                for i in range(1,5):
                    for nfins in fins:
                        print(f'Testing {prim}_n{nfins}_X{i}_Y{j} ...')
                        build_test( prim, n=nfins, X=i, Y=j)


