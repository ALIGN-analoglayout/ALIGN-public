import pathlib
import sys
import pytest
import json

pdks = []
for prim in (pathlib.Path(__file__).parent.parent.parent / 'pdks').iterdir():
    if prim.is_dir() and (prim / 'Align_primitives.py').exists():
        pdks.append(prim)
my_dir = pathlib.Path(__file__).resolve().parent


def check_shorts(cmdlist, constraints):
    from Align_primitives import main, gen_parser
    parser = gen_parser()
    args = parser.parse_args(cmdlist)
    if constraints[0]["parameters"].get("height", None) == 24:
        with pytest.raises(AssertionError):
            uc = main(args)
        return
    else:
        uc = main(args)
    assert len(uc.rd.shorts) == 0, uc.rd.shorts  # rd = RemoveDuplicates
    assert len(uc.rd.opens) == 0, uc.rd.opens
    assert len(uc.rd.different_widths) == 0, uc.rd.different_widths
    assert len(uc.rd.subinsts) == 2*args.Xcells* args.Ycells, uc.rd.subinsts
    common_centroid = set(['M1_X0_Y0', 'M2_X1_Y0', 'M2_X2_Y0', 'M1_X3_Y0', 'M2_X0_Y1',
                      'M1_X1_Y1', 'M1_X2_Y1', 'M2_X3_Y1'])
    if constraints[0]["parameters"].get("pattern", None) == "cc":
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
    elif constraints[0]["parameters"].get("pattern", None) == "ncc":
        assert uc.rd.subinsts.keys() == set(['M1_X0_Y0', 'M1_X1_Y0', 'M2_X2_Y0', 'M2_X3_Y0', 'M1_X0_Y1',
                                             'M1_X1_Y1', 'M2_X2_Y1', 'M2_X3_Y1']), f"non common centroid should be AABB"
    elif constraints[0]["parameters"].get("pattern", None) == "id":
        assert uc.rd.subinsts.keys() == set(['M1_X0_Y0', 'M2_X1_Y0', 'M1_X2_Y0', 'M2_X3_Y0', 'M2_X0_Y1',
                                             'M1_X1_Y1', 'M2_X2_Y1', 'M1_X3_Y1']), f"inter digitated pattern should be ABAB"
    elif constraints[0]["parameters"].get("shared_diff", None) == True:
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
        assert uc.rd.canvas.bbox.toList() == [0, 0, 1120, 3528], "shared device should have smaller area"
    elif constraints[0]["parameters"].get("shared_diff", None) == False:
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
        assert uc.rd.canvas.bbox.toList() == [0, 0, 2560, 3528]
    elif constraints[0]["parameters"].get("body", None) == True:
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
        assert uc.rd.canvas.bbox.toList() == [0, 0, 1120, 3528]
    elif constraints[0]["parameters"].get("body", None) == False:
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
        assert uc.rd.canvas.bbox.toList() == [0, 0, 1120, 2352]
        assert all(len(x.pins) == 3 for x in uc.rd.subinsts.values()), uc.rd.subinsts
    elif constraints[0]["parameters"].get("height", None) == 36:
        assert uc.rd.subinsts.keys() == common_centroid, f"common centroid should be ABBA"
        assert uc.rd.canvas.bbox.toList() == [0, 0, 1120, 4536]
    if constraints[0]["parameters"].get("body", None) != False:
        assert all(len(x.pins) == 4 for x in uc.rd.subinsts.values()), uc.rd.subinsts
    assert len(uc.drc.errors) == 0, uc.drc.errors


def build_test(pdk, prim, *, n, X, Y, constraints):
    sys.path.insert(0, str(pdk))
    b = f"{prim}_n{n}_X{X}_Y{Y}"
    #print(f'Testing {b} ...')
    my_dir.mkdir(parents=True, exist_ok=True)
    with open(my_dir / f'{prim}.const.json', 'w') as fp:
        fp.write(json.dumps(constraints, indent=2))
    check_shorts(['-p', prim, '-b', b, '-n', f"{n}", '-X', f"{X}", '-Y', f"{Y}" , '-c' , f"{my_dir}"], constraints)

    sys.path.pop(0)


supported_const = [{"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "cc"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "ncc"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"pattern": "id"}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"shared_diff": True}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"shared_diff": False}},
                    {"constraint": "Generator", "name": "MOS", "parameters": {"body": True}},
                   {"constraint": "Generator", "name": "MOS", "parameters": {"body": False}},
                   {"constraint": "Generator", "name": "MOS", "parameters": {"height": 24}},
                   {"constraint": "Generator", "name": "MOS", "parameters": {"height": 36}}
                   ]
@pytest.mark.parametrize("pdk", pdks, ids=lambda x: x.name)
@pytest.mark.parametrize("const", supported_const)
def test_mos_finfet_const(const):
    pdk = pathlib.Path('/mnt/d/research_work/ALIGN/mywork/ALIGN-public/pdks/FinFET14nm_Mock_PDK')
    x = 2
    y = 2
    nfins = 12
    prim = 'DP_NMOS'
    if 'FinFET14nm_Mock_PDK' in pdk:
        build_test(pdk, prim, n=nfins, X=x, Y=y, constraints=[const])
    if 'Bulk65nm_Mock_PDK' in pdk and supported_const.index(const)<3:
        build_test(pdk, prim, n=nfins, X=x, Y=y, constraints=[const])
