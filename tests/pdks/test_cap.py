import pathlib
import sys
import pytest

pdks = []
for pdk in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if pdk.is_dir() and (pdk / 'fabric_Cap.py').exists():
        pdks.append(pdk)


def check_shorts(cmdlist):
    from fabric_Cap import main, gen_parser
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.drc.errors) == 0, uc.drc.errors


def build_test(pdk, b, *, w, l):
    sys.path.insert(0, str(pdk))
    # print(str(pdk))
    check_shorts(['-b', b, '-w', f"{w}", '-l',f"{l}"])
    sys.path.pop(0)


@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_cap_smoke(pdk):
    l = 200
    w = 200
    build_test(pdk, f'cap_{w}_{l}', w=w, l=l)


@pytest.mark.nightly
@pytest.mark.parametrize("l", range(200, 1000, 400), ids=lambda x: f'n{x}')
@pytest.mark.parametrize("w", range(200, 1000, 400), ids=lambda x: f'n{x}')
@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
def test_cap_full(pdk, l, w):
    build_test(pdk, f'cap_{w}_{l}', w=w, l=l)
