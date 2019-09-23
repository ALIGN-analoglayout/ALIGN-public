from fabric_Cap import main, gen_parser

def check_shorts( cmdlist):
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0
    for op in uc.rd.opens:
        pass
        #assert op[0] in ['g','v0','fin','active','RVT']

def build_test( b, *, n):
    check_shorts( ['-b', b, '-n', f"{n}"])

def test_range():
    for i in range( 4, 32, 2):
        check_shorts( ['-b', f'cap_{i}', '--x_length', f"{i}", '--y_length', f"{i}"])


def test_small():
    build_test( 'cap_4fF', n=4)

def x_test_a0():
    build_test( 'cap_12fF', n=12)
def x_test_a1():
    build_test( 'cap_10fF', n=10)

