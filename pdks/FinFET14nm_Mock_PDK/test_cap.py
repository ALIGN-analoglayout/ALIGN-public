from fabric_Cap import main, gen_parser

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test( b, *, n):
    check_shorts( ['-b', b, '-n', f"{n}"])

def test_range():
    for i in range( 4, 32, 2):
        build_test( f'cap_{i}', n=i)


def test_small():
    build_test( 'cap_4fF', n=4)

def test_a0():
    build_test( 'cap_12fF', n=12)
def test_a1():
    build_test( 'cap_10fF', n=10)

