import os
import json
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits

CLEANUP = os.getenv("CLEANUP", True)
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


def test_cmp_reuse():
    name_1 = f'ckt_{get_test_id()}_1'
    name_2 = f'ckt_{get_test_id()}_2'

    netlist_1 = circuits.comparator(name_1)
    netlist_2 = circuits.comparator(name_2)

    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        # {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}
    ]
    example_1 = build_example(name_1, netlist_1, constraints)
    ckt_dir_1, run_dir_1 = run_example(example_1, n=1, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])

    name_1 = name_1.upper()
    with (run_dir_1 / '1_topology' / f'{name_1.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        constraints_1 = modules[name_1]["constraints"]

    example_2 = build_example(name_2, netlist_2, constraints_1)
    ckt_dir_2, run_dir_2 = run_example(example_2, n=1, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])

    name_2 = name_2.upper()
    with (run_dir_2 / '1_topology' / f'{name_2.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        constraints_2 = modules[name_2]["constraints"]
    assert len(constraints_1) == len(constraints_2)
    assert all(c in constraints_2 for c in constraints_1)

    if CLEANUP:
        shutil.rmtree(ckt_dir_1)
        shutil.rmtree(run_dir_1)
        shutil.rmtree(ckt_dir_2)
        shutil.rmtree(run_dir_2)
