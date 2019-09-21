from Align_primitives import main, gen_parser

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0
    for op in uc.rd.opens:
        assert op[0] in ['g','v0','fin','active','RVT']

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


