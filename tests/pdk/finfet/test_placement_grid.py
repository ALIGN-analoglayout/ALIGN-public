import json
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_place_on_grid():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    _, run_dir = run_example(example, cleanup=False)

    with (run_dir / '3_pnr' / 'Results' / f'{name.upper()}_0.placement_verilog.json').open('rt') as fp:
        d = json.load(fp)
        found = False
        for m in d['modules']:
            for i in m['instances']:
                if i['abstract_template_name'] == 'TFR_PRIM_L_1E06_W_1E06':
                    t = i['transformation']
                    assert t['sX'] == 1
                    assert t['sY'] == 1
                    assert t['oX'] % 12600 == 6300, f'primitive is not placed on grid {t}'
                    found = True
        assert found
