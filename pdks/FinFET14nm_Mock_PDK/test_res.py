from fabric_Res import main, gen_parser

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    # assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    # assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test( b, *, X, Y, n, r):
    check_shorts( ['-b', b, '-X', f'{X}', '-Y', f'{Y}', '-n', f'{n}', '-r', f'{r}'])

def test_range():
    for x in range(1,4):
        for y in range(1,4):
            for i in range(1,4):
                for j in range(400, 1000, 200):
                    build_test( f'res_X{x}_Y{y}_h{i}_r{j}', X=x, Y=y, n=i, r=j)

