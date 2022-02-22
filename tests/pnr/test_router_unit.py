import json
import pathlib
import os
import shutil
import datetime

from align.cell_fabric import pdk, gen_gds_json, gen_lef

import align

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path(os.environ['ALIGN_WORK_DIR']).resolve()
else:
    ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'


pdkdir = pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"

p = pdk.Pdk().load(pdkdir / 'layers.json')



def gen_it(run_dir, ctn, layout_d):

    with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
        json.dump(layout_d, fp=fp, indent=2)

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p, mode='placement')

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p)


def run_it(run_dir, nm, max_errors = 0):
    os.chdir(run_dir)

    args = ['dummy_input_directory_can_be_anything', '-s', nm, '--flow_start', '3_pnr', '--skipGDS']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f'No results for {nm}'

    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {nm} ({k})"
            assert v['errors'] <= max_errors, f"{nm} ({k}):Number of DRC errors: {str(v['errors'])}"


def test_horizontal_wire():
    nm = 'horizontal_wire'

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [{'formal': 'A0', 'actual': 'A'},
                       {'formal': 'A1', 'actual': 'A'}]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xhalfwidth = 16
    minlength = 180
    yhalfendtoend = 24

    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, ny * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend

    terminals = [
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    ]
    for x, net in [(1,"A0"), (nx-1,"A1")]:
        terminals.append( 
            {
                "layer": "M1",
                "netName": net,
                "rect": [x * xpitch - xhalfwidth, lly,
                         x * xpitch + xhalfwidth, ury],
                "netType": "pin"
            }
        )

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    gen_it(run_dir, 'leaf', layout_d)
    run_it(run_dir, nm)

def test_two_horizontal_wires():
    nm = 'two_horizontal_wires'

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [{'formal': 'A0', 'actual': 'A'},
                       {'formal': 'A1', 'actual': 'A'},
                       {'formal': 'B0', 'actual': 'B'},
                       {'formal': 'B1', 'actual': 'B'}
            ]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xhalfwidth = 16
    minlength = 180
    yhalfendtoend = 24

    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, ny * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend
    assert ury-lly >= minlength

    terminals = [
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    ]
    for x, net in [(1,"A0"), (nx-2,"A1"), (2, "B0"), (nx-1, "B1")]:
        terminals.append( 
            {
                "layer": "M1",
                "netName": net,
                "rect": [x * xpitch - xhalfwidth, lly,
                         x * xpitch + xhalfwidth, ury],
                "netType": "pin"
            }
        )

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    gen_it(run_dir, 'leaf', layout_d)
    run_it(run_dir, nm)

def test_three_horizontal_wires():
    nm = 'three_horizontal_wires'

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [{'formal': 'A0', 'actual': 'A'},
                       {'formal': 'A1', 'actual': 'A'},
                       {'formal': 'B0', 'actual': 'B'},
                       {'formal': 'B1', 'actual': 'B'},
                       {'formal': 'C0', 'actual': 'C'},
                       {'formal': 'C1', 'actual': 'C'}
            ]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xhalfwidth = 16
    minlength = 180
    yhalfendtoend = 24

    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, ny * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend
    assert ury-lly >= minlength

    terminals = [
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    ]
    for x, net in [(1,"A0"), (nx-3,"A1"), (2, "B0"), (nx-2, "B1"), (3, "C0"), (nx-1, "C1")]:
        terminals.append( 
            {
                "layer": "M1",
                "netName": net,
                "rect": [x * xpitch - xhalfwidth, lly,
                         x * xpitch + xhalfwidth, ury],
                "netType": "pin"
            }
        )

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    gen_it(run_dir, 'leaf', layout_d)
    run_it(run_dir, nm)


def test_four_horizontal_wires():
    nm = 'four_horizontal_wires'

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [{'formal': 'A0', 'actual': 'A'},
                       {'formal': 'A1', 'actual': 'A'},
                       {'formal': 'B0', 'actual': 'B'},
                       {'formal': 'B1', 'actual': 'B'},
                       {'formal': 'C0', 'actual': 'C'},
                       {'formal': 'C1', 'actual': 'C'},
                       {'formal': 'D0', 'actual': 'D'},
                       {'formal': 'D1', 'actual': 'D'}
            ]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xhalfwidth = 16
    minlength = 180
    yhalfendtoend = 24

    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, ny * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend
    assert ury-lly >= minlength

    terminals = [
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    ]
    for x, net in [(1,"A0"), (nx-4,"A1"), (2, "B0"), (nx-3, "B1"), (3, "C0"), (nx-2, "C1"), (4, "D0"), (nx-1, "D1")]:
        terminals.append( 
            {
                "layer": "M1",
                "netName": net,
                "rect": [x * xpitch - xhalfwidth, lly,
                         x * xpitch + xhalfwidth, ury],
                "netType": "pin"
            }
        )

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    gen_it(run_dir, 'leaf', layout_d)
    run_it(run_dir, nm, max_errors=1)

def test_four_horizontal_wires_extend():
    nm = 'four_horizontal_wires_extend'

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [{'formal': 'A0', 'actual': 'A'},
                       {'formal': 'A1', 'actual': 'A'},
                       {'formal': 'B0', 'actual': 'B'},
                       {'formal': 'B1', 'actual': 'B'},
                       {'formal': 'C0', 'actual': 'C'},
                       {'formal': 'C1', 'actual': 'C'},
                       {'formal': 'D0', 'actual': 'D'},
                       {'formal': 'D1', 'actual': 'D'}
            ]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xhalfwidth = 16
    minlength = 180
    yhalfendtoend = 24

    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, (ny + 1) * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend
    assert ury-lly >= minlength

    terminals = [
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    ]
    for x, net in [(1,"A0"), (nx-4,"A1"), (2, "B0"), (nx-3, "B1"), (3, "C0"), (nx-2, "C1"), (4, "D0"), (nx-1, "D1")]:
        terminals.append( 
            {
                "layer": "M1",
                "netName": net,
                "rect": [x * xpitch - xhalfwidth, lly,
                         x * xpitch + xhalfwidth, ury],
                "netType": "pin"
            }
        )

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    gen_it(run_dir, 'leaf', layout_d)
    run_it(run_dir, nm, max_errors=0)
