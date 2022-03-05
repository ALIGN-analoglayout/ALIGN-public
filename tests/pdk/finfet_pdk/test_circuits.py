import pytest
import json
import shutil
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits

cleanup = True


def test_cmp_vanilla():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, area=4.5e9)

    counter = len([fname.name for fname in (run_dir / '2_primitives').iterdir() if fname.name.startswith('DP_NMOS') and fname.name.endswith('.lef')])
    assert counter == 6, f'Diff pair in comparator should have 6 variants. Found {counter}.'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_cmp_vanilla_pg():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.skip(reason='This test is failing. Enable in a future PR after refactoring')
def test_cmp_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        for module in modules.values():
            assert len(module['constraints']) == 1, "Constraints generated despise AutoConstraint"

    if cleanup:
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
    run_example(example, cleanup=cleanup, area=4.5e9)


def test_cmp_fp1():
    name = f'ckt_{get_test_id()}'
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
    # Stop flow early for memory profiling
    run_example(example, cleanup=cleanup, area=4e10)
    # run_example(example, cleanup=cleanup, area=4e10, additional_args=['--flow_stop', '2_primitives'])
    # run_example(example, cleanup=cleanup, area=4e10, additional_args=['--flow_stop', '3_pnr:prep', '--router_mode', 'no_op'])


def test_cmp_fp2():
    name = f'ckt_{get_test_id()}'
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
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup, area=5e9)


def test_cmp_order():
    """ mp7 and mp8 should not be identified as a primitive """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [{"constraint": "Order", "direction": "left_to_right", "instances": ["mp7", "mp8"]}]
    name = f'ckt_{get_test_id()}'
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=['--flow_stop', '3_pnr:prep'])

    name = name.upper()
    with (run_dir / '1_topology' / f'{name}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        instances = set([k['instance_name'] for k in modules[name]['instances']])
        assert 'X_MP7' in instances and 'X_MP8' in instances, f'MP7 or MP8 not found in {instances}'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_ota_six_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


def test_ota_six():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": False},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.skip
def test_ldo_amp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


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
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '3_pnr' / 'inputs' / 'RO_STAGE.pnr.const.json').open('rt') as fp:
        d = json.load(fp)
        assert len(d['constraints']) > 0, 'Where is the order constraint???'

    if cleanup:
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
    run_example(example, cleanup=cleanup)


def test_two_stage_ota():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.two_stage_ota_differential(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.5, "ratio_high": 2.0},
        {"constraint": "GroupBlocks", "instances": ["xmn4", "xmn2"], "name": "scn"},
        {"constraint": "GroupBlocks", "instances": ["xmn1", "xmn0"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["xmp2", "xmp0"], "name": "scp"},
        {"constraint": "GroupBlocks", "instances": ["xmp3", "xmp1"], "name": "dp2"},
        {"constraint": "GroupBlocks", "instances": ["xmn5", "xmn3"], "name": "sc2"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["sc2", "dp2", "scp", "dp", "scn"], "abut": True},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["sc2"], ["dp2"], ["scp"], ["dp"], ["scn"]]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


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
    run_example(example, cleanup=False)


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
    run_example(example, cleanup=False)
