from fabric_Res import main, gen_parser

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    # assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    # assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test( b, *, n, r):
    check_shorts( ['-b', b, '-n', f"{n}", '-r', f"{r}"])

def test_range():
    for i in range(1,4):
        for j in range(400, 1000, 200):
            build_test( f'res_{i}_{j}', n=i, r=j)

