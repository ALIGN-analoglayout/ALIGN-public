import os
import json
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits
import textwrap

CLEANUP = False if os.getenv("CLEANUP", None) else True
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

    with (run_dir_1 / '1_topology' / f'{name_1.lower()}.const.json').open('rt') as fp:
        reusable_const = json.load(fp)

    example_2 = build_example(name_2, netlist_2, reusable_const)
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


def test_same_template_group_block():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vip von vop nbs vccx vssx
        mp0 von von vccx vccx p w=180e-9 nf=4 m=2
        mp1 vop von vccx vccx p w=180e-9 nf=4 m=2
        mn0 von vip vmp  vssx nlvt w=180e-9 nf=4 m=2
        mn1 vmp vip vcm  vssx n    w=180e-9 nf=4 m=2
        mn2 vop vin vmn  vssx nlvt w=180e-9 nf=4 m=2
        mn3 vmn vin vcm  vssx n    w=180e-9 nf=4 m=2
        mn4 vcm nbs vssx vssx n    w=180e-9 nf=4 m=2
        .ends {name}
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn0", "mn1"], "instance_name": "xdiff_left"},
        {"constraint": "GroupBlocks", "instances": ["mn2", "mn3"], "instance_name": "xdiff_right"},
        {"constraint": "SameTemplate", "instances": ["xdiff_left", "xdiff_right"]}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])

    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        instances = modules[name]["instances"]
        atn_l = [inst["abstract_template_name"] for inst in instances if inst["instance_name"] == "XDIFF_LEFT"][0]
        atn_r = [inst["abstract_template_name"] for inst in instances if inst["instance_name"] == "XDIFF_RIGHT"][0]
        assert atn_l == atn_r, f"Template names do not match: {atn_l=} vs {atn_r=}"

    if CLEANUP:
        shutil.rmtree(ckt_dir)
        shutil.rmtree(run_dir)
