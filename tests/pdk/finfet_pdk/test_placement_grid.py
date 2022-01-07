import json
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits


def test_place_on_grid():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=8)

    name = name.upper()
    for variant in range(8):
        filename = run_dir / '3_pnr' / 'Results' / f'{name}_{variant}.scaled_placement_verilog.json'
        print(f'Checking {filename}')
        with (filename).open('rt') as fp:
            verilog_json = json.load(fp)
            modules = {module['concrete_name']: module for module in verilog_json['modules']}
            cn = f'{name}_{variant}'
            assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
            instances = [i for i in modules[cn]['instances'] if i['abstract_template_name'] == 'TFR_PRIM_L_1E06_W_1E06']
            assert len(instances) == 1, 'There should be one resistor instance'
            for i in instances:
                t = i['transformation']
                # PlaceOnGrid(direction='H', pitch=2*row_height, ored_terms=[OffsetsScalings(offsets=[1*row_height], scalings=[1])]).dict()
                # PlaceOnGrid(direction='V', pitch=5*poly_pitch, ored_terms=[OffsetsScalings(offsets=[1*poly_pitch], scalings=[1])]).dict()
                row_height = 6300
                poly_pitch = 1080
                assert t['sX'] == 1
                assert t['sY'] == 1
                assert (t['oX'] - poly_pitch) % (5*poly_pitch) == 0, f"Illegal horizontal placement {t['oX']}"
                assert (t['oY'] - row_height) % (2*row_height) == 0, f"Illegal vertical placement {t['oY']}"


def test_scalings():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    mp0 o a vccx vccx p w=45e-9 m=1 nf=1
    mn0 o a vssx vssx n w=45e-9 m=1 nf=1
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    xi2 v2 vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "AlignInOrder", "line": "left", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=8)

    name = name.upper()
    for variant in range(8):
        filename = run_dir / '3_pnr' / 'Results' / f'{name}_{variant}.scaled_placement_verilog.json'
        if not filename.exists():
            break
        print(f'Checking {filename}')
        with (filename).open('rt') as fp:
            verilog_json = json.load(fp)
            modules = {module['concrete_name']: module for module in verilog_json['modules']}
            cn = f'{name}_{variant}'
            assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
            instances = [i for i in modules[cn]['instances'] if i['abstract_template_name'] == 'DIG22INV']
            assert len(instances) == 3, 'There should be three inverter instances'
            for i in instances:
                t = i['transformation']
                # PlaceOnGrid(direction='H', pitch=2*row_height, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1, -1])]).dict()
                row_height = 6300
                assert t['oY'] % (2*row_height) == 0, f"Illegal placement oY={t['oY']} is not a multiple of {2*row_height}"
