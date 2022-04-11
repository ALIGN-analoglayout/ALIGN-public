import time
import json
import pytest
import shutil
from .utils import build_example, run_example
from . import circuits
from align.pnr.hpwl import gen_netlist, calculate_HPWL_from_placement_verilog_d
from align.pnr.render_placement import standalone_overlap_checker


cleanup = True

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
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
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
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


# @pytest.mark.skipif(not BENCHMARK, reason="Exclude from CI")
@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b2(name, params):
    name = f'ckt_b2_{name}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn", "invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["ccp"], ["ccn"], ["dp"], ["mn0"], ["invn", "invp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"], "abut": True},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
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
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skipif(not BENCHMARK, reason="Exclude from CI")
@pytest.mark.parametrize(("name", "params"), PARAMS)
def test_b3(name, params):
    name = f'ckt_b3_{name}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7", "mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9", "mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn", "invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"], ["invn", "invp"], ["mp9", "mp10"], ["mp7", "mp8"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 1, "ratio_high": 2}
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
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
