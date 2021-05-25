import json
import pathlib
import io
import pytest
import os
import shutil
import datetime

from align.pnr.cmdline import cmdline
from align.cell_fabric import pdk, gen_gds_json, gen_lef

import align

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() 
else:
    ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'


pdkdir = pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"

p = pdk.Pdk().load(pdkdir / 'layers.json')

def test_row():
    nm = 'row'

    run_dir = ALIGN_WORK_DIR / f'{nm}_entrypoint2'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = []
    n = 3
    for i in range(n):
        inp = 'inp' if i==0   else f'x{i}'
        out = 'out' if i==n-1 else f'x{i+1}'
        instance = {
            'instance_name': f'u{i}',
            'abstract_template_name': 'slice',
            'fa_map': [ {'formal': 'inp', 'actual': inp},
                        {'formal': 'out', 'actual': out}]
        }    
        instances.append( instance)

    topmodule = {
        'name': nm,
        'parameters': ["inp","out"],
        'instances': instances,
        'constraints': [
            {
                'constraint': 'Order',
                'direction': 'left_to_right',
                'instances': [ f'u{i}' for i in range(n)]
            },
            {
                'constraint': 'SameTemplate',
                'instances': [ f'u{i}' for i in range(n)]
            }
        ]
    }

    verilog_d = { 'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm}.verilog.json').open('wt') as fp:
        json.dump( verilog_d, fp=fp, indent=2)


    primitives_d = {}
    
    for suffix in ['_a', '_b', '_c']:
        atn = 'slice'
        ctn = f'{atn}{suffix}'
        primitives_d[ctn] = { 'abstract_template_name': atn,
                              'concrete_template_name': ctn}

    with (run_dir / '1_topology' / f'__primitives__.json').open('wt') as fp:
        json.dump( primitives_d, fp=fp, indent=2)
    

    xpitch = 80
    ypitch = 84
    xstopdelta = 36
    yhalfwidth = 16

    sizes = [ ('_a', (10,10)),
              ('_b', ( 5,20)),
              ('_c', (20, 5))]

    for suffix, (nx,ny) in sizes:

        bbox = [0,0,nx*xpitch,ny*ypitch]

        sx,ex = 2,nx-2
        inp_y,out_y = 2,ny-2

        terminals = [
            {
                "layer": "M2",
                "netName": "inp",
                "pin": "inp",
                "rect": [sx*xpitch-xstopdelta, inp_y*ypitch-yhalfwidth,
                         ex*xpitch+xstopdelta, inp_y*ypitch+yhalfwidth]
            },
            {
                "layer": "M2",
                "netName": "out",
                "pin": "out",
                "rect": [sx*xpitch-xstopdelta, out_y*ypitch-yhalfwidth,
                         ex*xpitch+xstopdelta, out_y*ypitch+yhalfwidth]
            }
        ]

        layout_d = { 'bbox': bbox,
                     'globalRoutes': [],
                     'globalRouteGrid': [],
                     'terminals': terminals
        }

        ctn = f'slice{suffix}'

        with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
            json.dump( layout_d, fp=fp, indent=2)

        with (run_dir / '2_primitives' / f'{ctn}.json').open('rt') as fp0, \
             (run_dir / '2_primitives' / f'{ctn}.gds.json').open('wt') as fp1:
            gen_gds_json.translate(ctn, '', 0, fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0), p)

        gen_lef.json_lef( run_dir / '2_primitives' / f'{ctn}.json', ctn,
                          cell_pin=['inp','out'], bodyswitch=1, blockM=0, p=p)

    #==========================

    os.chdir(run_dir)

    (run_dir / 'inputs').mkdir(parents=False, exist_ok=False)

    args = [ 'inputs', '-s', nm, '--flow_start', '3_pnr']
    results = align.CmdlineParser().parse_args(args)
