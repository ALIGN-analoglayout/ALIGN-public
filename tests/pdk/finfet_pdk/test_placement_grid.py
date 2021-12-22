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
    constraints = []
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False)

    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in scaled_placement_verilog.json'
        found = False
        for i in modules[cn]['instances']:
            if i['abstract_template_name'] == 'TFR_PRIM_L_1E06_W_1E06':
                t = i['transformation']
                # PlaceOnGrid(direction='H', pitch=2*row_height, ored_terms=[OffsetsScalings(offsets=[1*row_height], scalings=[1])]).dict()
                # PlaceOnGrid(direction='V', pitch=5*poly_pitch, ored_terms=[OffsetsScalings(offsets=[1*poly_pitch], scalings=[1])]).dict()
                row_height = 6300
                poly_pitch = 1080
                assert t['sX'] == 1
                assert t['sY'] == 1
                assert (t['oX'] - poly_pitch) % (5*poly_pitch) == 0, f"Illegal horizontal placement {t['oX']}"
                assert (t['oY'] - row_height) % (2*row_height) == 0, f"Illegal vertical placement {t['oY']}"
                found = True
        assert found, 'No instances of tfr_prim in placement'
