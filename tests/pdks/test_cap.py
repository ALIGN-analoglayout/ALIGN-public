import os
import pathlib
import pytest
from .utils import get_test_id, WORK_DIR
import importlib

pdks = []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.stem == "Bulk45nm_Mock_PDK":
        continue
    if pdk.is_dir() and (pdk / 'fabric_Cap.py').exists():
        pdks.append(pdk)


def check_shorts(pdk, cmdlist):
    spec = importlib.util.spec_from_file_location("fabric_Cap", pdk / 'fabric_Cap.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    main = getattr(module, "main")
    gen_parser = getattr(module, "gen_parser")
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.drc.errors) == 0, uc.drc.errors


def build_test(pdk, b, *, w, l):
    cwd = pathlib.Path(os.getcwd())
    check_shorts(pdk, ['-b', b, '-w', f"{w}", '-l', f"{l}", '-o', f"{cwd}"])


@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_cap_smoke(pdk):
    test_dir = WORK_DIR / get_test_id()
    test_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(test_dir)
    l = 200
    w = 200
    build_test(pdk, f'cap_{w}_{l}', w=w, l=l)


@pytest.mark.nightly
@pytest.mark.parametrize("l", range(200, 1000, 400), ids=lambda x: f'l{x}')
@pytest.mark.parametrize("w", range(200, 1000, 400), ids=lambda x: f'w{x}')
@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_cap_full(pdk, l, w):
    test_dir = WORK_DIR / get_test_id()
    test_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(test_dir)
    build_test(pdk, f'cap_{w}_{l}', w=w, l=l)
