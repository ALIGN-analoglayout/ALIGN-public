import time
import json
import pytest
import shutil
from .utils import build_example, run_example, get_test_id
from . import circuits
from align.pnr.hpwl import gen_netlist, calculate_HPWL_from_placement_verilog_d
from align.pnr.render_placement import standalone_overlap_checker


CLEANUP = True

PARAMS = [
        ("tamu_sp", ["--router_mode", "no_op"]),
        ("umn_ilp", ["--router_mode", "no_op", "--place_using_ILP"])
]

BENCHMARK = False


# @pytest.mark.skipif(not BENCHMARK, reason="Exclude from CI")
@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b1(name, params):
    name = f'ckt_b1_{name}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xg1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xg2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xg3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xg3", "xg2", "xg1"]},
        {"constraint": "AspectRatio", "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    s = time.time()
    ckt_dir, run_dir = run_example(example, additional_args=params, cleanup=False)
    elapsed_time = time.time() - s
    cn = f'{name.upper()}_0'
    with (run_dir / '3_pnr' / 'Results' / f'{cn}.scaled_placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_new = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        x0, y0, x1, y1 = placement['modules'][0]['bbox']
        area_new = (x1-x0)*(y1-y0)
    print(f'\n{name}: AREA={area_new/1e8:0.2f} HPWL={hpwl_new/1e4:0.2f} TIME={elapsed_time:0.2f}')
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


# @pytest.mark.skipif(not BENCHMARK, reason="Exclude from CI")
@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b2(name, params):
    name = f'ckt_b2_{name}'
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
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["xccp"], ["xccn"], ["xdp"], ["mn0"], ["xinvn", "xinvp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "xccp", "xccn", "xdp", "mn0"], "abut": True},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    s = time.time()
    ckt_dir, run_dir = run_example(example, additional_args=params, cleanup=False)
    elapsed_time = time.time() - s
    cn = f'{name.upper()}_0'
    with (run_dir / '3_pnr' / 'Results' / f'{cn}.scaled_placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_new = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        x0, y0, x1, y1 = placement['modules'][0]['bbox']
        area_new = (x1-x0)*(y1-y0)
    print(f'\n{name}: AREA={area_new/1e8:0.2f} HPWL={hpwl_new/1e4:0.2f} TIME={elapsed_time:0.2f}')
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skipif(not BENCHMARK, reason="Exclude from CI")
@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b3(name, params):
    name = f'ckt_b3_{name}'
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
        {"constraint": "AspectRatio", "ratio_low": 1, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    s = time.time()
    ckt_dir, run_dir = run_example(example, additional_args=params, cleanup=False)
    elapsed_time = time.time() - s
    cn = f'{name.upper()}_0'
    with (run_dir / '3_pnr' / 'Results' / f'{cn}.scaled_placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_new = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        x0, y0, x1, y1 = placement['modules'][0]['bbox']
        area_new = (x1-x0)*(y1-y0)
    print(f'\n{name}: AREA={area_new/1e8:0.2f} HPWL={hpwl_new/1e4:0.2f} TIME={elapsed_time:0.2f}')
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b4(name, params):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.charge_pump_switch(name, size=8)
    constraints = {
        name: [
            {"constraint": "PowerPorts", "ports": ["vccx"]},
            {"constraint": "GroundPorts", "ports": ["vssx"]}
        ],
        "switch": [
            {"constraint": "DoNotIdentify", "instances": ["qp0", "qn0"]}
        ]
    }
    example = build_example(name, netlist, constraints)
    s = time.time()
    ckt_dir, run_dir = run_example(example, additional_args=params, cleanup=False)
    elapsed_time = time.time() - s
    cn = f'{name.upper()}_0'
    with (run_dir / '3_pnr' / 'Results' / f'{cn}.scaled_placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        assert standalone_overlap_checker(placement, cn)
        nets = gen_netlist(placement, cn)
        hpwl_new = calculate_HPWL_from_placement_verilog_d(placement, cn, nets)
        x0, y0, x1, y1 = placement['modules'][0]['bbox']
        area_new = (x1-x0)*(y1-y0)
    print(f'\n{name}: AREA={area_new/1e8:0.2f} HPWL={hpwl_new/1e4:0.2f} TIME={elapsed_time:0.2f}')
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
