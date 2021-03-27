import pathlib
import sys
import pytest

pdks= []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.is_dir() and (pdk / 'fabric_Res.py').exists():
        pdks.append(pdk)

def check_shorts( cmdlist):
    from fabric_Res import main, gen_parser
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    # assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    # assert len(uc.drc.errors) == 0, uc.drc.errors

def build_test(pdk, b, *, X, Y, n, r):
    sys.path.insert(0, str(pdk))
    #print(str(pdk))
    check_shorts( ['-b', b, '-X', f'{X}', '-Y', f'{Y}', '-n', f'{n}', '-r', f'{r}'])
    sys.path.pop(0)

@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_res_smoke(pdk):
    x = 2
    y = 2
    n = 2
    r = 400
    build_test(pdk, f'res_X{x}_Y{y}_h{n}_r{r}', X=x, Y=y, n=n, r=r)

@pytest.mark.nightly
@pytest.mark.parametrize( "r", range(400, 1000, 200), ids=lambda x: f'r{x}')
@pytest.mark.parametrize( "n", range(1,4), ids=lambda x: f'n{x}')
@pytest.mark.parametrize( "y", range(1,4), ids=lambda x: f'Y{x}')
@pytest.mark.parametrize( "x", range(1,4), ids=lambda x: f'X{x}')
@pytest.mark.parametrize( "pdk", pdks, ids=lambda x: x.name)
def test_res(pdk, x, y, n, r):
    build_test(pdk, f'res_X{x}_Y{y}_h{n}_r{r}', X=x, Y=y, n=n, r=r)
