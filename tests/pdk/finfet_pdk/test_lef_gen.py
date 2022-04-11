import pytest
import json
import shutil
import textwrap
import os
from .utils import get_test_id, build_example, run_example
from . import circuits

CLEANUP = True
LOG_LEVEL = 'INFO'

align_home = os.getenv('ALIGN_HOME')

def test_obs_lef():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=1, cleanup=False, log_level=LOG_LEVEL)
    cmd = f'{align_home}/bin/gen_lef_with_obs.py -l {run_dir}/3_pnr/inputs/layers.json -g {run_dir}/3_pnr/Results/{name.upper()}_0.gds.json -f {run_dir}/{name.upper()}_0.lef'
    os.system(cmd)
    with (run_dir / f'{name.upper()}_0_obs.lef').open('rt') as fpo, (run_dir / f'{name.upper()}_0.lef').open('rt') as fp:
        datao, data = fpo.read(), fp.read()
        assert(datao.count('M4') > data.count('M4')) # all power grid shapes should be in the obstacle lef file

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


