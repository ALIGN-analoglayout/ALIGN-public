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


def test_flow_start_primitives():

    nm = 'five_transistor_ota'
    run_dir = ALIGN_WORK_DIR / f'{nm}_flow_start_primitives'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    os.chdir(run_dir)

    args = ['../../examples/five_transistor_ota', '--flow_stop', '1_topology']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    args = ['../../examples/five_transistor_ota', '--flow_start', '2_primitives']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None

    
