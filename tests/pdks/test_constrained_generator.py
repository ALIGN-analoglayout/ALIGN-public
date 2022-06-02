import pathlib
import sys
import pytest
import json

pdks = []
for prim in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if prim.is_dir() and (prim / 'Align_primitives.py').exists():
        pdks.append(prim)
my_dir = pathlib.Path(__file__).resolve().parent / 'tmp'


def get_xcells_pattern(primitive, pattern, x_cells):
    # TODO: remove this name based multiplier for number of cells
    if any(primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*x_cells + 2
    elif any(primitive.startswith(f'{x}_') for x in ["SCM", "CMC", "DP", "CCP", "LS"]):
        # Dual transistor primitives
        x_cells = 2*x_cells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells % 4 != 0 else pattern  # CC is not possible; default is interdigitated
    return x_cells, pattern

def check_shorts(cmdlist):
    from Align_primitives import main, gen_parser
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.rd.different_widths) == 0, uc.rd.different_widths
    assert len(uc.rd.subinsts) == get_xcells_pattern(args.primitive, args.pattern, args.Xcells)[0] * args.Ycells, uc.rd.subinsts
    assert all(len(x.pins) == 4 for x in uc.rd.subinsts.values()), uc.rd.subinsts
    assert len(uc.drc.errors) == 0, uc.drc.errors


def build_test(pdk, prim, *, n, X, Y, constraints):
    sys.path.insert(0, str(pdk))
    b = f"{prim}_n{n}_X{X}_Y{Y}"
    #print(f'Testing {b} ...')
    my_dir.mkdir(parents=True, exist_ok=True)
    with open(my_dir / f'{prim}.const.json', 'w') as fp:
        fp.write(json.dumps(constraints, indent=2))
    check_shorts(['-p', prim, '-b', b, '-n', f"{n}", '-X', f"{X}", '-Y', f"{Y}" , '-c' , f"{my_dir}"])
    sys.path.pop(0)


supported_const = [{"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "cc"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "ncc"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "id"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"shared_diff": True}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"shared_diff": False}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"parallel_wires": {"DA": 2, "DB":2}}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"body": True}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"body": False}}
                   ]
# @pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
@pytest.mark.parametrize("const", supported_const)
def test_mos_smoke(const):
    pdk = pathlib.Path('/mnt/d/research_work/ALIGN/mywork/ALIGN-public/pdks/FinFET14nm_Mock_PDK')
    x = 2
    y = 2
    nfins = 12
    prim = 'DP_NMOS'
    build_test(pdk, prim, n=nfins, X=x, Y=y, constraints=[const])


@pytest.mark.nightly
@pytest.mark.parametrize("y", range(4, 5), ids=lambda x: f'Y{x}')
@pytest.mark.parametrize("x", range(4, 5), ids=lambda x: f'X{x}')
@pytest.mark.parametrize("nfins", [12], ids=lambda x: f'n{x}')
@pytest.mark.parametrize("typ", ["NMOS", "PMOS"])
@pytest.mark.parametrize("pstr", [
    "{}_4T",
    "DCL_{}",
    "SCM_{}",
    "CMC_{}",
    "DP_{}"],
    ids=lambda x: x.replace('_{}', ''))
@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
@pytest.mark.parametrize("const", supported_const)
def test_mos_full(pdk, pstr, typ, nfins, x, y, const):
    prim = pstr.format(typ)
    build_test(pdk, prim, n=nfins, X=x, Y=y, constraints=[const])

