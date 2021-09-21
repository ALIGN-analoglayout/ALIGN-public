import pytest
import textwrap
import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits

cleanup = False


def test_cmp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


def test_cmp_pg():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


def test_cmp_pg_clk():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        CLOCK = clk
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"], ["invn", "invp"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6}
    ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "name": "invp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "name": "invn"},
        {"constraint": "SameTemplate", "instances": ["mp7","mp8"]},
        {"constraint": "SameTemplate", "instances": ["mp9","mp10"]},
        {"constraint": "SameTemplate", "instances": ["invn","invp"]},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["ccp"], ["ccn"], ["dp"], ["mn0"], ["invn", "invp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 1.5}
    ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_3():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        CLOCK = clk
        """)
    constraints = [
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["mn0"], ["dp"]]},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["ccp"], ["ccn"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp", "ccn"]}
    ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.nightly
def test_cmp_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        DONT_CONST = {name}
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
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
    setup = ""
    constraints = [{"constraint": "Order", "direction": "left_to_right", "instances": ["mp7", "mp8"]}]
    name = f'ckt_{get_test_id()}'
    example = build_example(name, netlist, setup, constraints)
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
    setup = ""
    constraints = [{"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 1.5}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)


@pytest.mark.skip
def test_ldo_amp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_USE_CELLS = CASCODED_CMC_NMOS CMB_PMOS_2 LSB_PMOS_2 LSB_NMOS_2
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)
