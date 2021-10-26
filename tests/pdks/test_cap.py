import pathlib
import sys
import pytest

pdks= []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.is_dir() and (pdk / 'fabric_Cap.py').exists():
        pdks.append(pdk)

def check_shorts( cmdlist):
    from fabric_Cap import main, gen_parser
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test(pdk, b, *, n):
    sys.path.insert(0, str(pdk))
    #print(str(pdk))
    check_shorts(['-b', b, '-n', f"{n}"])
    sys.path.pop(0)

@pytest.mark.parametrize( "pdk", pdks, ids=lambda x: x.name)
def test_cap_smoke(pdk):
    n = 4
    build_test(pdk, f'cap_{4}', n=4)

@pytest.mark.nightly
@pytest.mark.parametrize( "n", range( 4, 32, 2), ids=lambda x: f'n{x}')
@pytest.mark.parametrize( "pdk", pdks, ids=lambda x: x.name)
def test_cap_full(pdk, n):
    build_test(pdk, f'cap_{n}', n=n)
