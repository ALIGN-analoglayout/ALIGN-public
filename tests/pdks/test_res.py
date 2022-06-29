import os
import pathlib
import pytest
from .utils import get_test_id, WORK_DIR
import importlib

pdks = []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.is_dir() and (pdk / 'fabric_Res.py').exists():
        pdks.append(pdk)


def check_shorts(pdk, cmdlist):
    spec = importlib.util.spec_from_file_location("fabric_Res", pdk / 'fabric_Res.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    main = getattr(module, "main")
    gen_parser = getattr(module, "gen_parser")
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    # assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    # assert len(uc.drc.errors) == 0, uc.drc.errors


def build_test(pdk, b, *, X, Y, n, r):
    cwd = pathlib.Path(os.getcwd())
    check_shorts(pdk, ['-b', b, '-X', f'{X}', '-Y', f'{Y}', '-n', f'{n}', '-r', f'{r}', '-o', f"{cwd}"])


@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_res_smoke(pdk):
    test_dir = WORK_DIR / get_test_id()
    test_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(test_dir)
    x = 2
    y = 2
    n = 2
    r = 400
    build_test(pdk, f'res_X{x}_Y{y}_h{n}_r{r}', X=x, Y=y, n=n, r=r)


@pytest.mark.nightly
@pytest.mark.parametrize("r", range(400, 1000, 200), ids=lambda x: f'r{x}')
@pytest.mark.parametrize("n", range(1, 4), ids=lambda x: f'n{x}')
@pytest.mark.parametrize("y", range(1, 4), ids=lambda x: f'Y{x}')
@pytest.mark.parametrize("x", range(1, 4), ids=lambda x: f'X{x}')
@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_res(pdk, x, y, n, r):
    test_dir = WORK_DIR / get_test_id()
    test_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(test_dir)
    build_test(pdk, f'res_X{x}_Y{y}_h{n}_r{r}', X=x, Y=y, n=n, r=r)
