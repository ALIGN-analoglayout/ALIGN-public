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


def test_flow_each_step():

    nm = 'five_transistor_ota'
    #nm = 'switched_capacitor_filter'
    run_dir = ALIGN_WORK_DIR / f'{nm}_flow_each_step'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    os.chdir(run_dir)

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_stop', '1_topology']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_start', '2_primitives', '--flow_stop', '2_primitives']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_start', '3_pnr:prep', '--flow_stop', '3_pnr:prep']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_start', '3_pnr:place', '--flow_stop', '3_pnr:place']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_start', '3_pnr:gui', '--flow_stop', '3_pnr:gui']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = [f'{ALIGN_HOME}/examples/{nm}', '--flow_start', '3_pnr:route']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    
