import os
import json
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits
import logging
logger = logging.getLogger(__name__)

CLEANUP = False
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


def test_cmp_clk():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp",  "generator":{ "name": "MOS"}},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn", "generator":{ "name": "MOS"} },
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp", "generator":{ "name": "MOS"}},
        {"constraint": "DoNotIdentify", "instances": ["mn11", "mn12", "mp13", "mp14"]},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "Floorplan", "order": True, "symmetrize": True, "regions": [
            ["mp7", "mp9", "mp10", "mp8"],
            ["mp13", "xccp", "mp14"],
            ["mn11", "xccn", "mn12"],
            ["xdp"],
            ["mn0"]
            ]},
        {"constraint": "AspectRatio", "ratio_low": 0.5, "ratio_high": 2}
    ]

    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL)
    name = name.upper()
    with (run_dir / '3_pnr' / f'{name}_0.json').open('rt') as fp:
        data = json.load(fp)
        for term in data['terminals']:
            if term['netName'] == 'CLK':
                assert term["layer"] != "M4"

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
