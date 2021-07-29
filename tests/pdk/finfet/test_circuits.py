import json
import shutil
import pytest
import textwrap
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_comparator():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = constraints = ""
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


@pytest.mark.nightly
def test_comparator_1():
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
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.7, "ratio_high": 1.3}
    ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


@pytest.mark.nightly
def test_comparator_2():
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
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["ccp"], ["ccn"], ["dp"], ["mn0"], ["invn", "invp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "ccp", "ccn", "dp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["invn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.5, "ratio_high": 1.5}
    ]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


@pytest.mark.nightly
def test_comparator_clk():
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
    run_example(example)


@pytest.mark.nightly
def test_comparator_noconst():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        NO_CONST = {name}
        """)
    constraints = "[]"
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


@pytest.mark.nightly
def test_comparator_order():
    """ mp7 and mp8 should not bypass subcircuit identification """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = ""
    constraints = [{"constraint": "Order", "direction": "left_to_right", "instances": ["mmp7", "mmp8"]}]
    name = f'ckt_{get_test_id()}'
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_ota_six():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    setup = ""
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_ldo_opamp_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = [{"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}]
    example = build_example(name, netlist, setup, constraints)
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
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_USE_CELLS = CASCODED_CMC_NMOS CMB_PMOS_2 LSB_PMOS_2 LSB_NMOS_2
        """)
    constraints = [{"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}]
    example = build_example(name, netlist, setup, constraints)
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
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        DONT_USE_CELLS = CASCODED_CMC_NMOS CMB_PMOS_2 LSB_PMOS_2 LSB_NMOS_2
        NO_CONST = {name}
        """)
    constraints = [
        {"constraint": "AspectRatio", "subcircuit": "ldo_opamp", "ratio_low": 0.5, "ratio_high": 2.0}
        # ,{"constraint": "GroupBlocks", "instances": ["mp29", "mp30"], "name": "cp2"}
        ]
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, max_errors=100, n=1)
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        abstract_names = set([instance['abstract_name'] for instance in placement['leaves']])
        prim = 'CMC_S_PMOS_B_plplvt_w2160_m1_nf12'
        assert prim in abstract_names, f'{prim} not found in placement'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_ldo_opamp_4():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_opamp(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        DONT_USE_CELLS = CASCODED_CMC_NMOS CMB_PMOS_2 LSB_PMOS_2 LSB_NMOS_2
        """)
    constraints = [
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2.0},
        {"constraint": "GroupBlocks", "instances": ["xmn1", "xmn2"], "name": "dp"},
        {"constraint": "GroupBlocks", "instances": ["xmp3", "xmp4"], "name": "cm1"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "cm2"},
        {"constraint": "GroupBlocks", "instances": ["xmn7", "xmn8"], "name": "cm3"},
        {"constraint": "GroupBlocks", "instances": ["xmn9", "xmn10"], "name": "cm4"},
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["cm1"], ["cm2"], ["cm3"], ["cm4"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "abut": True, "instances": ["cm1", "cm2", "cm3", "cm4"]},
        {"constraint": "GroupBlocks", "instances": ["mp11", "xmp12", "xmp13", "xmn14", "xmn15","mn16", "mp17", "mn18", "mp19", "mp20", "xmn40"], "name": "buf"},
        {"constraint": "GroupBlocks", "instances": ["xmn105", "xmn101", "mn102", "xmn103", "mp103", "xmp104"], "name": "bias"},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["dp", "cm1", "buf"]},
        {"constraint": "Order", "direction": "top_to_bottom", "abut": True, "instances": ["dp", "bias"]}
    ]
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)
    with (run_dir / '3_pnr' / f'{name}_0.json').open('rt') as fp:
        data = json.load(fp)
        for term in data['terminals']:
            if term['layer'].startswith('M') and term['netName'] is not None:
                assert '/' not in term['netName'], f'Broken connectivity: {term}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
