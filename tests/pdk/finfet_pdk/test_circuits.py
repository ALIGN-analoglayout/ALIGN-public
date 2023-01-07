from collections import defaultdict
import re
import os
import pytest
import json
import shutil
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits
import logging
logger = logging.getLogger(__name__)

CLEANUP = False if os.getenv("CLEANUP", None) else True
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


def test_cmp_vanilla():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=1, cleanup=False, log_level=LOG_LEVEL, additional_args=["--router_mode", "bottom_up", "--placer_sa_iterations", "1000"])
    counter = len([fname.name for fname in (run_dir / '2_primitives').iterdir() if fname.name.startswith('DP_NMOS') and fname.name.endswith('.lef')])
    assert counter == 6, f'Diff pair in comparator should have 6 variants. Found {counter}.'
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason='This test is failing. Enable in a future PR after refactoring')
def test_cmp_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL)
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        for module in modules.values():
            assert len(module['constraints']) == 1, "Constraints generated despise AutoConstraint"
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason='This test is failing. Enable in a future PR after refactoring')
def test_cmp_noconst_pg():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, area=4.5e9, log_level=LOG_LEVEL)


def test_cmp_fp1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "instance_name": "xinvp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "instance_name": "xinvn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["xinvn", "xinvp"]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["xdp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["xccp"], ["xccn"], ["xinvn", "xinvp"], ["mp9", "mp10"], ["mp7", "mp8"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "xdp"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["xdp", "xccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 1, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    # Stop flow early for memory profiling
    run_example(example, cleanup=CLEANUP, area=4e10, log_level=LOG_LEVEL, additional_args=["--router_mode", "bottom_up", "--placer_sa_iterations", "1000"])
    # run_example(example, cleanup=CLEANUP, area=4e10, additional_args=['--flow_stop', '2_primitives'])
    # run_example(example, cleanup=CLEANUP, area=4e10, additional_args=['--flow_stop', '3_pnr:prep', '--router_mode', 'no_op'])


def test_cmp_fp2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "instance_name": "xinvp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "instance_name": "xinvn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["xinvn", "xinvp"]},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["xccp"], ["xccn"], ["xdp"], ["mn0"], ["xinvn", "xinvp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "xccp", "xccn", "xdp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, area=5e9, log_level=LOG_LEVEL, additional_args=["--router_mode", "bottom_up", "--placer_sa_iterations", "1000"])


def test_cmp_fp2_regions():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp"},
        {"constraint": "DoNotIdentify", "instances": ["mn11", "mn12", "mp13", "mp14"]},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "Floorplan", "order": True, "symmetrize": True, "regions": [
            ["mp7", "mp9", "mp10", "mp8"],
            ["mp13", "xccp", "mp14"],
            ["mn11", "xccn", "mn12"],
            ["xdp"],
            ["mn0"]
        ]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, area=5e9, log_level=LOG_LEVEL)


def test_cmp_order():
    """ mp7 and mp8 should not be identified as a primitive """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [{"constraint": "Order", "direction": "left_to_right", "instances": ["mp7", "mp8"]}]
    name = f'ckt_{get_test_id()}'
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=['--flow_stop', '3_pnr:prep'], log_level=LOG_LEVEL)

    name = name.upper()
    with (run_dir / '1_topology' / f'{name}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        instances = set([k['instance_name'] for k in modules[name]['instances']])
        assert 'X_MP7' in instances and 'X_MP8' in instances, f'MP7 or MP8 not found in {instances}'

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_ota_six_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP)


def test_ota_six():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xtail"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xdiffpair"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xload"},
        {"constraint": "Floorplan", "order": True, "symmetrize": True, "regions": [["xload"], ["xdiffpair"], ["xtail"]]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL)


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP)


def test_ldo_amp_simple():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp_simple(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, max_errors=1,
                additional_args=["--placer_sa_iterations", "100", "--router_mode", "no_op"])


def test_ldo_amp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL,
                additional_args=["--placer_sa_iterations", "100", '--router_mode', 'no_op'])


def test_ro_simple():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ro_simple(name)
    constraints = {
        'ro_stage': [
            {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mp0", "mn0"]},
        ],
        name: [
            {"constraint": "Order", "direction": "left_to_right", "instances": [f'xi{k}' for k in range(5)]},
        ]
    }
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL)

    with (run_dir / '3_pnr' / 'inputs' / 'RO_STAGE.pnr.const.json').open('rt') as fp:
        d = json.load(fp)
        assert len(d['constraints']) > 0, 'Where is the order constraint???'

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_common_source():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source_mini(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AlignInOrder", "line": "left", "instances": ["mp0", "mn0"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL)


def test_two_stage_ota():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.two_stage_ota_differential(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.5, "ratio_high": 2.0},
        {"constraint": "GroupBlocks", "instances": ["xmn4", "xmn2"], "instance_name": "xscn"},
        {"constraint": "GroupBlocks", "instances": ["xmn1", "xmn0"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["xmp2", "xmp0"], "instance_name": "xscp"},
        {"constraint": "GroupBlocks", "instances": ["xmp3", "xmp1"], "instance_name": "xdp2"},
        {"constraint": "GroupBlocks", "instances": ["xmn5", "xmn3"], "instance_name": "xsc2"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xsc2", "xdp2", "xscp", "xdp", "xscn"], "abut": True},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["xsc2"], ["xdp2"], ["xscp"], ["xdp"], ["xscn"]]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL)


def test_cs_1():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=180e-9 nf=4 m=1
        mn0 vop vin vssx vssx n w=180e-9 nf=4 m=1
        .ends {name}
        """)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL)


def test_cs_2():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=180e-9 nf=4 m=2
        mn0 vop vin vssx vssx n w=180e-9 nf=4 m=2
        .ends {name}
        """)
    constraints = [{"constraint": "MultiConnection", "nets": ["vop"], "multiplier": 2}]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL)


def test_charge_pump_switch():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.charge_pump_switch(name, size=16)
    constraints = {
        name: [
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "ConfigureCompiler", "same_template": True}
        ],
        "switch": [
            {"constraint": "DoNotIdentify", "instances": ["qp0", "qn0"]}
        ]
    }
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=8, cleanup=False, log_level=LOG_LEVEL, additional_args=['--flow_stop', '3_pnr:prep', '--router_mode', 'bottom_up'])
    name = name.upper()
    with (run_dir / "1_topology" / f"{name}.verilog.json").open("rt") as fp:
        hierarchy = json.load(fp)
        module = [m for m in hierarchy["modules"] if m["name"] == name][0]
        same_template = [c for c in module["constraints"] if c["constraint"] == "SameTemplate"]
        assert len(same_template) == 2, "Duplicate SameTemplate constraints"
        align_in_order = [c for c in module["constraints"] if c["constraint"] == "AlignInOrder"]
        assert len(align_in_order) == 1, "AlignInOrder not found"

    with (run_dir / "3_pnr" / "inputs" / f"{name}.pnr.const.json").open("rt") as fp:
        charge_pump_const = json.load(fp)
        same_template = [c for c in charge_pump_const["constraints"] if c["const_name"] == "SameTemplate"]
        assert len(same_template) == 1, "Duplicate SameTemplate constraints"

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_charge_pump_switch_small():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.charge_pump_switch(name, size=4)
    constraints = {
        name: [
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "ConfigureCompiler", "same_template": True}
        ],
        "switch": [
            {"constraint": "DoNotIdentify", "instances": ["qp0", "qn0"]}
        ]
    }
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=8, cleanup=False, log_level=LOG_LEVEL, additional_args=['--flow_stop', '1_Topology', '--router_mode', 'bottom_up'])
    name = name.upper()
    with (run_dir / "1_topology" / f"{name}.verilog.json").open("rt") as fp:
        hierarchy = json.load(fp)
        module = [m for m in hierarchy["modules"] if m["name"] == name][0]
        same_template = [c for c in module["constraints"] if c["constraint"] == "SameTemplate"]
        assert len(same_template) == 1, "SameTemplate constraint not found!"

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_niwc_opamp_split():
    # Tests legal size and exact_patterns restrictions

    name = f'ckt_{get_test_id()}'
    netlist = circuits.niwc_opamp_split(name)
    constraints = [
    {"constraint": "ConfigureCompiler", "auto_constraint": False, "merge_parallel_devices": False},
    {"constraint": "Route", "min_layer": "M2", "max_layer": "M3"},
    {"constraint": "PowerPorts", "ports": ["vccx"]},
    {"constraint": "GroundPorts", "ports": ["vssx"]},
    {"constraint": "GroupBlocks", "instances": ["mtail"], "instance_name": "xmtail0", "template_name":"mtail0",
     "generator": { "name": "MOS", "parameters": { "PARTIAL_ROUTING": True, "single_device_connect_m1": False, "legal_sizes": [{"y": 8}]}}},
        {"constraint": "GroupBlocks", "instances": ["m1", "m2"], "instance_name": "xdp", "template_name":"dp",
     "generator": { "name": "MOS", "parameters": { "exact_patterns": [["AbBa",
                                                                       "BaAb",
                                                                       "BaAb",
								       "AbBa"]], "PARTIAL_ROUTING": True}}},
        {"constraint": "GroupBlocks", "instances": ["m7a", "m8a"], "instance_name": "xnraila", "template_name":"nraila", "generator": {"name": "MOS",
                   "parameters": {"pattern_template": ["AbBa",
		                                        "BaAb"], "PARTIAL_ROUTING": True, "legal_sizes": [{"y": 8}]}}},
        {"constraint": "GroupBlocks", "instances": ["m7b", "m8b"], "instance_name": "xnrailb", "template_name":"nrailb",
     "generator": {"name": "MOS",
                   "parameters": {"pattern_template": ["AbBa",
 		                                       "BaAb"], "PARTIAL_ROUTING": True, "legal_sizes": [{"y": 8}]}}},
        {"constraint": "GroupBlocks", "instances": ["m11", "m12"], "instance_name": "xprail", "template_name":"prail",
     "generator": {"name": "MOS",
                   "parameters": {"pattern_template": ["AbBa",
		                                       "BaAb"], "PARTIAL_ROUTING": True, "legal_sizes": [{"y": 8}]}}},
        {"constraint": "GroupBlocks", "instances": ["m3a", "m4a"], "instance_name": "xlsa",
            "template_name":"lsa", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 4}]}}},
    {"constraint": "GroupBlocks", "instances": ["m3b", "m4b"], "instance_name": "xlsb", "template_name":"lsb","generator": { "name": "MOS", "parameters": {"legal_sizes": [{"y": 4}]}}},
    {"constraint": "GroupBlocks", "instances": ["m5a", "m6a"], "instance_name": "xostagea", "template_name":"ostagea","generator": { "name": "MOS", "parameters": {"legal_sizes": [{"y": 4}]}}},
        {"constraint": "GroupBlocks", "instances": ["m5b", "m6b"], "instance_name": "xostageb",
            "template_name":"ostageb", "generator": {"name": "MOS", "parameters": {"legal_sizes": [{"y": 4}]}}},
    {"constraint": "SameTemplate", "instances": ["xlsa", "xlsb"]},
    {"constraint": "SameTemplate", "instances": ["xostagea", "xostageb"]},
    {"constraint": "SameTemplate", "instances": ["xnraila", "xnrailb"]},
    {"constraint": "Floorplan",
     "order": True,
     "symmetrize": True,
     "regions": [
        ["xprail"],
        ["xostagea", "xlsa", "xdp", "xlsb", "xostageb"],
        ["xnraila", "xmtail0", "xnrailb"]
     ]},
    {"constraint": "MultiConnection", "nets": ["tail"], "multiplier": 4}
]

    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=8, cleanup=False, log_level=LOG_LEVEL, additional_args=['--flow_stop', '3_pnr:place'])

    pat = re.compile(r"^(.*)_(\d+)_X(\d+)_Y(\d+)$")

    size_tbl = defaultdict(list)

    for file in (run_dir / "2_primitives").glob('*.json'):
        if file.suffixes == [".json"]:
            m = pat.match(file.stem)
            if m:
                nm = m.groups()[0]
                x = int(m.groups()[2])
                y = int(m.groups()[3])
                size_tbl[nm].append((x,y))

    assert size_tbl['DP'] == [(2,4)]
    assert size_tbl['MTAIL0'] == [(4, 8)]
    assert size_tbl['PRAIL'] == [(4, 8)]
    assert size_tbl['LSA'] == [(1, 4)]
    assert size_tbl['LSB'] == [(1, 4)]
    assert size_tbl['OSTAGEA'] == [(1, 4)]
    assert size_tbl['OSTAGEB'] == [(1, 4)]
    assert size_tbl['NRAILA'] == [(1, 8)]
    assert size_tbl['NRAILB'] == [(1, 8)]

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_niwc_opamp_split_reuse():
    # Tests legal size and exact_patterns restrictions

    name = f'ckt_{get_test_id()}'
    netlist = circuits.niwc_opamp_split(name)
    constraints = [
  {"constraint": "ConfigureCompiler", "auto_constraint": False, "merge_parallel_devices": False},
  {"constraint": "Route", "min_layer": "M2", "max_layer": "M3"},
  {"constraint": "PowerPorts", "ports": ["vccx"]},
  {"constraint": "GroundPorts", "ports": ["vssx"]},
  {"constraint": "GroupBlocks", "instance_name": "X_M7A_M8A", "instances": ["M7A", "M8A"], "template_name": "CMC_NMOS", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M7B_M8B", "instances": ["M7B", "M8B"], "template_name": "CMC_NMOS", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M11_M12", "instances": ["M11", "M12"], "template_name": "CMC_PMOS", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M5A_M6A", "instances": ["M5A", "M6A"], "template_name": "CMC_S_NMOS_B", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M5B_M6B", "instances": ["M5B", "M6B"], "template_name": "CMC_S_NMOS_B", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M1_M2", "instances": ["M1", "M2"], "template_name": "DP_NMOS_B", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_MTAIL", "instances": ["MTAIL"], "template_name": "NMOS_3T", "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M3A_M4A", "instances": ["M3A", "M4A"], "generator": {"name": "mos", "parameters": None}},
  {"constraint": "GroupBlocks", "instance_name": "X_M3B_M4B", "instances": ["M3B", "M4B"], "generator": {"name": "mos", "parameters": None}},
  {"constraint": "SymmetricBlocks", "direction": "V",
   "pairs": [
       ["X_M5A_M6A", "X_M5B_M6B"]
   ]
  },
  {"constraint": "SymmetricBlocks", "direction": "V",
   "pairs": [
       ["X_M7A_M8A", "X_M7B_M8B"]
   ]
  }
]

    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, n=8, cleanup=False, log_level=LOG_LEVEL, additional_args=['--flow_stop', '3_pnr:place'])

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_opamp_poor():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.opamp_poor(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "SameTemplate", "instances": ["iloadl<0>", "iloadl<1>", "iloadr<0>", "iloadr<1>"]},
        {"constraint": "SameTemplate", "instances": ["idiffl<0>", "idiffl<1>", "idiffr<0>", "idiffr<1>"]},
        {"constraint": "SameTemplate", "instances": ["ibias<0>", "ibias<1>", "ibias<2>", "ibias<3>", "ibias<4>", "itail", "i1"]},
        {"constraint": "Floorplan",
            "order": True,
            "regions": [
                ["iloadl<0>", "iloadr<0>"],
                ["iloadr<1>", "iloadl<1>"],
                ["idiffl<0>", "idiffr<0>"],
                ["idiffr<1>", "idiffl<1>"],
                ["ibias<0>", "ibias<1>", "ibias<2>", "itail", "ibias<3>", "ibias<4>"]
            ]}
    ]
    example = build_example(name, netlist, constraints)
    # TODO: increase n after #1083 is fixed
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, n=1, additional_args=["--router_mode", "bottom_up", "--placer_sa_iterations", "1000"])


def test_comparator_analog():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator_analog(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["pinp", "pinn"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["nldl", "nldr"], "instance_name": "xcm"},
        {"constraint": "GroupBlocks", "instances": ["invp1", "invp1"], "instance_name": "xinv0"},
        {"constraint": "GroupBlocks", "instances": ["invp2", "invp2"], "instance_name": "xinv1"},
        {"constraint": "DoNotIdentify", "instances": ["sw_pbias_en", "sw_pullup_enb", "sw_pulldn_en", "sw_pulldn_en1"]},
        {"constraint": "Floorplan",
            "order": True,
            "regions": [
                ["decap0"],
                ["mpbias", "ptail", "p2", "sw_pbias_en"],
                ["xdp", "sw_pullup_enb"],
                ["xcm", "n2", "sw_pulldn_en", "sw_pulldn_en1"],
                ["decap1"],
                ["mp_hi", "nres1", "nres0"],
            ]},
        {"constraint": "Floorplan",
            "order": True,
            "symmetrize": True,
            "regions": [
                ["decap0"],
                ["ptail"],
                ["xdp"],
                ["xcm"],
                ["decap1"]
            ]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, n=1, additional_args=["--router_mode", "bottom_up", "--placer_sa_iterations", "1000"], max_errors=1)


def test_analog_mux_4to1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.analog_mux_4to1(name)
    constraints = {
        "passgate": [
            {"constraint": "GroupBlocks", "instances": ["qp1"], "instance_name": "xqp1",
                "generator": {"name": "MOS", "parameters": {"PARTIAL_ROUTING": True, "add_tap": False, "legal_sizes": [{"y": 1}]}}},
            {"constraint": "GroupBlocks", "instances": ["qn1"], "instance_name": "xqn1",
                "generator": {"name": "MOS", "parameters": {"PARTIAL_ROUTING": True, "add_tap": False, "legal_sizes": [{"y": 1}]}}},
            {"constraint": "Floorplan", "regions": [["xqp1"], ["xqn1"]]}
            ],
        "decoder_2to4": [
            {"constraint": "Floorplan", "order": True, "regions": [
                ["inv08", "inv09"],
                ["nand0", "inv00"],
                ["nand1", "inv01"],
                ["nand2", "inv02"],
                ["nand3", "inv03"]
                ]}
            ],
        name: [
            {
                "constraint": "ConfigureCompiler",
                "auto_constraint": False,
                "propagate": True,
                "fix_source_drain": False,
                "merge_series_devices": False,
                "merge_parallel_devices": False,
                "remove_dummy_devices": True,
                "remove_dummy_hierarchies": False
            },
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]},
            {"constraint": "DoNotRoute", "nets": ["vssx", "vccx"]},
            {"constraint": "SameTemplate", "instances": ["pg0", "pg1", "pg2", "pg3"]},
            {"constraint": "AlignInOrder", "line": "left", "instances": ["pg0", "pg1", "pg2", "pg3"], "abut": True},
            {"constraint": "AlignInOrder", "line": "bottom", "instances": ["i0", "pg3"]}
            ]
    }
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, n=1, max_errors=4)


def test_folded_cascode():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.folded_cascode(name)
    constraints = [
        {
            "constraint": "ConfigureCompiler",
            "auto_constraint": False,
            "propagate": True,
            "fix_source_drain": False,
            "merge_series_devices": False,
            "merge_parallel_devices": False,
            "remove_dummy_devices": True,
            "remove_dummy_hierarchies": False
        },
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vssx", "vccx"]},
        {"constraint": "GroupBlocks", "instances": ["qp4", "qp3"], "instance_name": "xqp4",
            "generator": {"name": "MOS", "parameters": {"place_on_grid": True, "add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qp2", "qp1"], "instance_name": "xqp2",
            "generator": {"name": "MOS", "parameters": {"add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qn4", "qn3"], "instance_name": "xqn4",
            "generator": {"name": "MOS", "parameters": {"add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qn6", "qn5"], "instance_name": "xqn6",
            "generator": {"name": "MOS", "parameters": {"place_on_grid": True, "add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qn1", "qn2"], "instance_name": "xdp",
            "generator": {"name": "MOS", "parameters": {"add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qp5<0>"], "instance_name": "xqp5<0>",
            "generator": {"name": "MOS", "parameters": {"place_on_grid": True, "add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qp5<1>"], "instance_name": "xqp5<1>",
            "generator": {"name": "MOS", "parameters": {"place_on_grid": True, "add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qp6<0>"], "instance_name": "xqp6<0>",
            "generator": {"name": "MOS", "parameters": {"add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "GroupBlocks", "instances": ["qp6<1>"], "instance_name": "xqp6<1>",
            "generator": {"name": "MOS", "parameters": {"add_tap": False, "legal_sizes": [{"y": 2}]}}},
        {"constraint": "SameTemplate", "instances": ["xqp5<0>", "xqp5<1>"]},
        {"constraint": "SameTemplate", "instances": ["xqp6<0>", "xqp6<1>"]},
        {
            "constraint": "Floorplan",
            "order": True,
            "symmetrize": True,
            "regions": [
                ["xqp5<0>", "xqp6<0>", "xqp6<1>", "xqp5<1>"],
                ["xqn6"],
                ["xqn4"],
                ["xqp2"],
                ["xqp4"],
                ["xdp"]
            ]
        }
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, n=1)


def test_binary():
    name = "binary"
    netlist = textwrap.dedent(f"""\
        .subckt power_cell vg vccx vcca
        xmp0 vcca vg vccx vccx ppv drain=gnd m=1 nf=4 source=pwr nfin=4
        .ends
        .subckt {name} vccx vcca vg[0]
        xi0 vccx vccx vcca power_cell
        xi1 vg[0] vccx vcca power_cell
        .ends {name}
        .END
    """)

    constraints = {
        "power_cell": [
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vcca"]},
            {"constraint": "DoNotRoute", "nets": ["vccx", "vcca"]}
        ],
        name: [
            {
                "constraint": "ConfigureCompiler",
                "propagate": True,
                "auto_constraint": False,
                "identify_array": False,
                "fix_source_drain": False,
                "merge_series_devices": False,
                "merge_parallel_devices": False,
                "remove_dummy_devices": False,
                "remove_dummy_hierarchies": False,
                "fix_source_drain": False
            },
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vcca"]},
            {"constraint": "DoNotRoute", "nets": ["vccx", "vcca"]},
            {
                "constraint": "Floorplan",
                "order": True,
                "regions": [
                    ["xi0"],
                    ["xi1"],
                ]
            }
        ]
    }

    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, log_level="DEBUG")

    with (run_dir / '1_topology' / 'power_cell.const.json').open('rt') as fp:
        constraints = json.load(fp)
        constraints = {c["constraint"]: c for c in constraints}
        assert "VG" not in constraints["PowerPorts"]["ports"], "VG is not a power port"
