from Align_primitives import main, gen_parser

def check_shorts( cmdline):
    parser = gen_parser()
    lst = [ x for x in cmdline.split(' ') if x != '']
    args = parser.parse_args(lst)
    uc = main(args)
    assert len(uc.rd.shorts) == 0
    for open in uc.rd.opens:
        assert open[0] in ['g','v0','fin','active','RVT']


def test_a0():
    check_shorts( "-p Switch_PMOS -b Switch_PMOS_n12_X1_Y1 -n 12 -X 1 -Y 1")
def test_a1():
    check_shorts( "-p Switch_NMOS -b Switch_NMOS_n12_X3_Y3 -n 12 -X 3 -Y 3")
def test_a2():
    check_shorts( "-p DCL_NMOS -b DCL_NMOS_n12_X2_Y1 -n 12 -X 2 -Y 1")
def test_a3():
    check_shorts( "-p Switch_NMOS -b Switch_NMOS_n12_X3_Y1 -n 12 -X 3 -Y 1")
def test_a4():
    check_shorts( "-p Switch_PMOS -b Switch_PMOS_n12_X2_Y1 -n 12 -X 2 -Y 1")
def test_a5():
    check_shorts( "-p CMC_PMOS_S -b CMC_PMOS_S_n12_X1_Y1 -n 12 -X 1 -Y 1")
def test_a6():
    check_shorts( "-p DP_NMOS -b DP_NMOS_n12_X3_Y3 -n 12 -X 3 -Y 3")
def test_a7():
    check_shorts( "-p CMFB_NMOS -b CMFB_NMOS_n12_X3_Y1 -n 12 -X 3 -Y 1")
def test_a8():
    check_shorts( "-p CMC_PMOS -b CMC_PMOS_n12_X2_Y1 -n 12 -X 2 -Y 1")
def test_a9():
    check_shorts( "-p CMC_NMOS -b CMC_NMOS_n12_X3_Y1 -n 12 -X 3 -Y 1")

