import json
import shutil
import pytest
import textwrap
import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example, plot_sa_cost, plot_sa_seq
    from . import circuits
except ImportError:
    from utils import get_test_id, build_example, run_example, plot_sa_cost, plot_sa_seq
    import circuits

cleanup = False


def test_cmp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, area=4.5e9)

    # TODO: Generalize this test to all primitives based on m value
    with (run_dir / '1_topology' / '__primitives__.json').open('rt') as fp:
        primitives = json.load(fp)
        counter = 0
        for m in primitives.keys():
            if m.startswith('DP_NMOS'):
                counter += 1
        assert counter == 6, f'Diff pair in comparator should have 6 variants. Found {counter}.'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.nightly
def test_cmp_pg():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_pg_clk():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ClockPorts", "ports": ["CLK"]}
    ]
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
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
    run_example(example, cleanup=cleanup, area=4e10)


@pytest.mark.nightly
def test_cmp_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
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
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 1.5}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup, area=5e9)


@pytest.mark.nightly
def test_cmp_3():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "ClockPorts", "ports": ["CLK"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup, area=3.5e9)


@pytest.mark.nightly
def test_cmp_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "AutoConstraint", "isTrue": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        module_found = False
        for module in verilog_json['modules']:
            if module['name'] == name.upper():
                module_found = True
            assert len(module['constraints']) == 0, "Constraints generated despise DONT_CONST"
        assert module_found, f'Module {name.upper()} not found in {name.upper()}verilog.json'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.nightly
def test_cmp_order():
    """ mp7 and mp8 should not be identified as a primitive """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [{"constraint": "Order", "direction": "left_to_right", "instances": ["mp7", "mp8"]}]
    name = f'ckt_{get_test_id()}'
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        module_found = False
        for module in verilog_json['modules']:
            if module['name'] == name.upper():
                module_found = True
                instances = set([k['instance_name'] for k in module['instances']])
                assert 'MP7' in instances and 'MP8' in instances, f'MP7 or MP8 not found in {instances}'
        assert module_found, f'Module {name.upper()} not found in {name.upper()}verilog.json'

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_ota_six():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.01, "ratio_high": 100}]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup, log_level='DEBUG')
    # plot_sa_cost(name.upper())
    # plot_sa_seq(name.upper())


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)


def test_ldo_opamp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    # constraints = [{"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}]
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)
    with (run_dir / '3_pnr' / f'{name}_0.json').open('rt') as fp:
        data = json.load(fp)
        for term in data['terminals']:
            if term['layer'].startswith('M') and term['netName'] is not None:
                assert '/' not in term['netName'], f'Broken connectivity: {term}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ldo_opamp_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]},
        {"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)
    with (run_dir / '3_pnr' / f'{name}_0.json').open('rt') as fp:
        data = json.load(fp)
        for term in data['terminals']:
            if term['layer'].startswith('M') and term['netName'] is not None:
                assert '/' not in term['netName'], f'Broken connectivity: {term}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ldo_opamp_3():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "AutoConstraint", "isTrue": False},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]},
        {"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}
        # ,{"constraint": "GroupBlocks", "instances": ["mp29", "mp30"], "name": "cp2"}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, max_errors=100, n=1)
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        abstract_names = set([instance['abstract_name'] for instance in placement['leaves']])
        prim = 'CMC_S_PMOS_B_P_w2160_m1_nf12'
        assert prim in abstract_names, f'{prim} not found in placement'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ldo_opamp_4():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "DoNotUseLib", "libraries": ["CASCODED_CMC_NMOS", "CMB_PMOS_2", "LSB_PMOS_2", "LSB_NMOS_2"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2.0},
        {"constraint": "GroupBlocks", "instances": ["xmn1", "xmn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["xmp3", "xmp4"], "name": "cm1"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "cm2"},
        {"constraint": "GroupBlocks", "instances": ["xmn7", "xmn8"], "name": "cm3"},
        {"constraint": "GroupBlocks", "instances": ["xmn9", "xmn10"], "name": "cm4"},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["cm1"], ["cm2"], ["cm3"], ["cm4"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "abut": True, "instances": ["cm1", "cm2", "cm3", "cm4"]},
        {"constraint": "GroupBlocks", "instances": ["mp11", "xmp12", "xmp13", "xmn14",
                                                    "xmn15", "mn16", "mp17", "mn18", "mp19", "mp20", "xmn40"], "name": "buf"},
        {"constraint": "GroupBlocks", "instances": ["xmn105", "xmn101", "mn102", "xmn103", "mp103", "xmp104"], "name": "bias"},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["dp", "cm1", "buf"]},
        {"constraint": "Order", "direction": "top_to_bottom", "abut": True, "instances": ["dp", "bias"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)
    with (run_dir / '3_pnr' / f'{name}_0.json').open('rt') as fp:
        data = json.load(fp)
        for term in data['terminals']:
            if term['layer'].startswith('M') and term['netName'] is not None:
                assert '/' not in term['netName'], f'Broken connectivity: {term}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ro_1():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt ro_stage vi vo vccx vssx
    mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
    mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
    .ends
    .subckt {name} vo vccx vssx
    xi0 vo v1 vccx vssx ro_stage
    xi1 v1 v2 vccx vssx ro_stage
    xi2 v2 v3 vccx vssx ro_stage
    xi3 v3 v4 vccx vssx ro_stage
    xi4 v4 vo vccx vssx ro_stage
    .ends {name}
    """)
    constraints = {
        'ro_stage': [
            {"constraint": "Order", "direction": "left_to_right", "instances": ["mn0", "mp0"]},
        ],
        name: [
            {"constraint": "AutoConstraint", "isTrue": False},
            {"constraint": "Order", "direction": "left_to_right", "instances": [f'xi{k}' for k in range(5)]},
        ]
    }
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=cleanup)

    with (run_dir / '3_pnr' / 'inputs' / 'RO_STAGE.pnr.const.json').open('rt') as fp:
        d = json.load(fp)
        assert len(d['constraints']) > 0, 'Where is the order constraint???'
