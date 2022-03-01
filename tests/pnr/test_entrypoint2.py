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


def gen_row_module(nm, n=3):
    instances = []
    for i in range(n):
        inp = 'INP' if i == 0 else f'X{i}'
        out = 'OUT' if i == n - 1 else f'X{i+1}'
        instance = {
            'instance_name': f'U{i}',
            'abstract_template_name': 'SLICE',
            'fa_map': [{'formal': 'INP', 'actual': inp},
                       {'formal': 'OUT', 'actual': out}]
        }
        instances.append(instance)

    topmodule = {
        'name': nm,
        'parameters': ["INP", "OUT"],
        'instances': instances,
        'constraints': [
            {
                'constraint': 'Order',
                'direction': 'left_to_right',
                'instances': [f'U{i}' for i in range(n)],
                'abut': False
            }
        ]
    }

    topmodule['constraints'].append(
        {
            'constraint': 'SameTemplate',
            'instances': [f'U{i}' for i in range(n)]
        }
    )

    return topmodule


def gen_matrix_module(nm, row_nm, n=3):
    instances = []
    for i in range(n):
        inp = 'INP' if i == 0 else f'X{i}'
        out = 'OUT' if i == n - 1 else f'X{i+1}'
        instance = {
            'instance_name': f'U{i}',
            'abstract_template_name': row_nm,
            'fa_map': [{'formal': 'INP', 'actual': inp},
                       {'formal': 'OUT', 'actual': out}]
        }
        instances.append(instance)

    topmodule = {
        'name': nm,
        'parameters': ["INP", "OUT"],
        'instances': instances,
        'constraints': [
            {
                'constraint': 'Order',
                'direction': 'top_to_bottom',
                'instances': [f'U{i}' for i in range(n)],
                'abut': False
            }
        ]
    }

    topmodule['constraints'].append(
        {
            'constraint': 'SameTemplate',
            'instances': [f'U{i}' for i in range(n)]
        }
    )

    return topmodule


def gen_primitives(run_dir):
    primitives_library = []
    primitives_d = {}

    sizes = [('_A', (10, 10, 1)),
             ('_B', (5, 20, 1)),
             ('_C', (20, 5, 1))]

    for suffix, _ in sizes:
        atn = 'SLICE'
        ctn = f'{atn}{suffix}'
        primitives_library.append({
                            'name': ctn,
                             'pins': ['INP', 'OUT'],
                             'generator': {'name':atn},
                             })
        primitives_d[ctn] = {'abstract_template_name': atn,
                             'concrete_template_name': ctn}

    with (run_dir / '1_topology' / '__primitives_library__.json').open('wt') as fp:
        json.dump(primitives_library, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    xpitch = 80
    ypitch = 84
    xstopdelta = 36
    yhalfwidth = 16

    for suffix, (nx, ny, sY) in sizes:

        bbox = [0, 0, nx * xpitch, ny * ypitch]

        sx, ex = 2, nx - 2
        inp_y, out_y = (2, ny - 2) if sY == 1 else (ny - 2, 2)

        terminals = [
            {
                "layer": "M2",
                "netName": "INP",
                "rect": [sx * xpitch - xstopdelta, inp_y * ypitch - yhalfwidth,
                         ex * xpitch + xstopdelta, inp_y * ypitch + yhalfwidth],
                "netType": "pin"
            },
            {
                "layer": "M2",
                "netName": "OUT",
                "rect": [sx * xpitch - xstopdelta, out_y * ypitch - yhalfwidth,
                         ex * xpitch + xstopdelta, out_y * ypitch + yhalfwidth],
                "netType": "pin"
            }
        ]

        layout_d = {'bbox': bbox,
                    'globalRoutes': [],
                    'globalRouteGrid': [],
                    'terminals': terminals
                    }

        atn = 'SLICE'
        ctn = f'{atn}{suffix}'

        with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
            json.dump(layout_d, fp=fp, indent=2)

        with (run_dir / '2_primitives' / f'{ctn}.json').open('rt') as fp0, \
             (run_dir / '2_primitives' / f'{ctn}.gds.json').open('wt') as fp1:
            gen_gds_json.translate(ctn, '', 0, fp0, fp1, datetime.datetime(2019, 1, 1, 0, 0, 0), p)

        gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                         bodyswitch=1, blockM=0, p=p, mode='placement')

        gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                         bodyswitch=1, blockM=0, p=p)


def test_row():
    nm = 'row'

    run_dir = ALIGN_WORK_DIR / f'{nm}_entrypoint2'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    topmodule = gen_row_module(nm.upper())

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    gen_primitives(run_dir)

    # ==========================

    os.chdir(run_dir)

    args = ['dummy_input_directory_can_be_anything', '-s', nm, '--flow_start', '3_pnr', '--skipGDS']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None


def test_matrix():
    row_nm = 'row'
    nm = 'matrix'

    run_dir = ALIGN_WORK_DIR / f'{nm}_entrypoint2'
    print(run_dir)
    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    rowmodule = gen_row_module(row_nm.upper(), n=3)
    topmodule = gen_matrix_module(nm.upper(), row_nm.upper(), n=4)

    verilog_d = {'modules': [topmodule, rowmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    gen_primitives(run_dir)

    # ==========================

    os.chdir(run_dir)

    args = ['dummy_input_directory_can_be_anything', '-s', nm, '--flow_start', '3_pnr', '--skipGDS']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None
