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

    wrapper_module = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [wrapper_module], 'global_signals': []}

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

    suffix = ''
    nx, ny = 20, 4

    bbox = [0, 0, nx * xpitch, ny * ypitch]

    lly, ury = yhalfendtoend, ny*ypitch - yhalfendtoend

    sx, ex = 1, nx - 1

    terminals = [
        {
            "layer": "M1",
            "netName": "A0",
            "rect": [sx * xpitch - xhalfwidth, lly,
                     sx * xpitch + xhalfwidth, ury],
            "netType": "pin"
        },
        {
            "layer": "M1",
            "netName": "A1",
            "rect": [ex * xpitch - xhalfwidth, lly,
                     ex * xpitch + xhalfwidth, ury],
            "netType": "pin"
        }
    ]

    layout_d = {'bbox': bbox,
                'globalRoutes': [],
                'globalRouteGrid': [],
                'terminals': terminals
                }

    ctn = 'leaf'

    with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
        json.dump(layout_d, fp=fp, indent=2)

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p, mode='placement')

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p)

    # ==========================

    os.chdir(run_dir)

    args = ['dummy_input_directory_can_be_anything', '-s', nm, '--flow_start', '3_pnr', '--skipGDS']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None
