import json
import shutil
import pytest
import textwrap
from align.pdk.finfet import CanvasPDK
from align.pnr.main import load_constraint_files, gen_constraint_files
from align.schema.hacks import VerilogJsonTop
from .utils import get_test_id, build_example, run_example, _count_pattern
from . import circuits


def test_aspect_ratio_low():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 3}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=1)
    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
        x0, y0, x1, y1 = modules[cn]['bbox']
        assert (x1-x0)/(y1-y0) >= 3
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_aspect_ratio_high():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "AspectRatio", "subcircuit": name, "ratio_high": 1}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=1)
    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
        x0, y0, x1, y1 = modules[cn]['bbox']
        assert (x1-x0)/(y1-y0) <= 1
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_aspect_ratio_failure():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source(name)
    constraints = [
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_high": 0.2},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.1}
    ]
    example = build_example(name, netlist, constraints)
    with pytest.raises(Exception):
        run_example(example, n=1)


def test_boundary_max_width():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "Boundary", "subcircuit": name, "max_width": 3.5}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_boundary_max_height():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    constraints = [{"constraint": "Boundary", "subcircuit": name, "max_height": 1.3}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_do_not_identify():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_five(name)
    constraints = [{"constraint": "AlignInOrder", "line": "left", "instances": ["mp1", "mn1"]}]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_order_abut():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["VCCX"]},
        {"constraint": "GroundPorts", "ports": ["VSSX"]},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "instance_name": "xdp"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "instance_name": "xccn"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "instance_name": "xccp"},
        {"constraint": "GroupBlocks", "instances": ["mn11", "mp13"], "instance_name": "xinvp"},
        {"constraint": "GroupBlocks", "instances": ["mn12", "mp14"], "instance_name": "xinvn"},
        {"constraint": "SymmetricBlocks", "direction": "V",
            "pairs": [["xccp"], ["xccn"], ["xdp"], ["mn0"], ["xinvn", "xinvp"], ["mp7", "mp8"], ["mp9", "mp10"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "xccp", "xccn", "xdp", "mn0"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["xinvn", "mp9", "mp7", "mn0"]},
        {"constraint": "MultiConnection", "nets": ["vcom"], "multiplier": 6},
        {"constraint": "AspectRatio", "subcircuit": "comparator", "ratio_low": 0.5, "ratio_high": 1.5},
        {"constraint": "Order", "abut": True, "direction": "left_to_right", "instances": ["xinvn", "xinvp"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_align_top_right():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=8
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=6
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=4
        .ends {name}
        """)
    constraints = [
        {"constraint": "AlignInOrder", "direction": "vertical", "line": "right", "instances": ["mn0", "mn1"]},
        {"constraint": "AlignInOrder", "direction": "horizontal", "line": "top", "instances": ["mn1", "mp1"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_align_center():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=8
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=6
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=16
        .ends {name}
        """)
    constraints = [
        {"constraint": "AlignInOrder", "direction": "vertical", "line": "center", "instances": ["mn0", "mn1", "mp1"]}
        ]
    example = build_example(name, netlist, constraints)
    run_example(example)


def test_donotroute():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt inv vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt {name} vi vo vccx vssx
        xi0 vi v1 vccx vssx inv
        xi1 v1 vo vccx vssx inv
        .ends
        """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["v1", "vccx", "vssx"]}
        ]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False)

    # There should be opens in the generated layout
    with (run_dir / '3_pnr' / f'{name.upper()}_0.json').open('rt') as fp:
        d = json.load(fp)

        cv = CanvasPDK()
        cv.terminals = d['terminals']
        cv.removeDuplicates()
        assert len(cv.rd.opens) > 0, 'Layout should have opens'

    # The generated and loaded files should be identical
    input_dir = run_dir / '3_pnr' / 'inputs'
    verilog_d = VerilogJsonTop.parse_file(input_dir / f'{name.upper()}.verilog.json')
    pnr_const_ds_l = load_constraint_files(input_dir)
    pnr_const_ds_g = gen_constraint_files(verilog_d, input_dir)
    assert pnr_const_ds_l == pnr_const_ds_g


def test_netpriority():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt inv vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt buf vi vo1 vo2 vccx vssx
        xi0 vi vo1 vccx vssx inv
        xi1 vi vo2 vccx vssx inv
        .ends
        .subckt {name} vi vccx vssx
        xi0 vi v1 v2 vccx vssx buf
        xi1 v1 vo1 vccx vssx inv
        xi2 v2 vo2 vccx vssx inv
        .ends
        """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]},
        {"constraint": "SameTemplate", "instances": ["xi1", "xi2"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["xi0", "xi1"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["xi0", "xi2"]},
        {"constraint": "Align", "line": "h_bottom", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "NetPriority", "nets": ["v1"], "weight": 0}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
        for inst in modules[cn]['instances']:
            if 'xi1' in inst['instance_name'].lower():
                xi1_ox = inst['transformation']['oX']
            if 'xi2' in inst['instance_name'].lower():
                xi2_ox = inst['transformation']['oX']
        assert xi2_ox < xi1_ox, f'xi2 (oX={xi2_ox}) should be left of xi1 (oX={xi1_ox})'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_placecloser():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt inv vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt buf vi vo1 vo2 vccx vssx
        xi0 vi vo1 vccx vssx inv
        xi1 vi vo2 vccx vssx inv
        .ends
        .subckt {name} vi vccx vssx
        xi0 vi v1 v2 vccx vssx buf
        xi1 v1 vo1 vccx vssx inv
        xi2 v2 vo2 vccx vssx inv
        .ends
        """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]},
        {"constraint": "SameTemplate", "instances": ["xi1", "xi2"]},
        {"constraint": "Align", "line": "h_bottom", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "PlaceCloser", "instances": ["xi1", "xi2"]}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
        for inst in modules[cn]['instances']:
            if 'xi0' in inst['instance_name'].lower():
                xi0_ox = inst['transformation']['oX']
            if 'xi1' in inst['instance_name'].lower():
                xi1_ox = inst['transformation']['oX']
            if 'xi2' in inst['instance_name'].lower():
                xi2_ox = inst['transformation']['oX']
        assert (xi0_ox < xi1_ox and xi0_ox < xi2_ox) or (xi0_ox > xi1_ox and xi0_ox > xi2_ox),\
            f'xi0 {xi0_ox} should be far left of far right of xi1 {xi1_ox} and xi2 {xi2_ox}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason='Failing test to be enabled in a follow up next PR')
def test_portlocation():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt inv vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt {name} vi v1 v2 vccx vssx
        xi0 vi vm vccx vssx inv
        xi1 vm v1 vccx vssx inv
        xi2 vm v2 vccx vssx inv
        .ends
        """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]},
        {"constraint": "SameTemplate", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "Align", "line": "h_bottom", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "PortLocation", "ports": ["v1"], "location": "RC"}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    name = name.upper()
    with (run_dir / '3_pnr' / 'Results' / f'{name}_0.scaled_placement_verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['concrete_name']: module for module in verilog_json['modules']}
        cn = f'{name}_0'
        assert cn in modules, f'{cn} not found in *.scaled_placement_verilog.json'
        for inst in modules[cn]['instances']:
            if 'xi0' in inst['instance_name'].lower():
                xi0_ox = inst['transformation']['oX']
            if 'xi1' in inst['instance_name'].lower():
                xi1_ox = inst['transformation']['oX']
            if 'xi2' in inst['instance_name'].lower():
                xi2_ox = inst['transformation']['oX']
        assert (xi0_ox < xi1_ox and xi2_ox < xi1_ox),\
            f'xi1 {xi1_ox} should be far right of xi0 {xi0_ox} and xi2 {xi2_ox}'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason="For next PR")
def test_enumerate():
    '''
        Test SP enumerator in placement. Two stacked transistor can be placed in at least 3 ways
        SS D1 | SS D2
        SS D1 | D2 SS
        D1 SS | SS D2
    '''
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt p_stack d g s b
        .param m=1
        mi2 i g s b p w=180e-9 m=1 nf=1
        mi1 d g i b p w=180e-9 m=1 nf=1
        .ends p_stack
        .subckt {name} d1 d2 ss vccx
        xmp1 d1 vg ss vccx p_stack m=1
        xmp2 d2 vg ss vccx p_stack m=1
        .ends
        """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx"]},
        {"constraint": "SameTemplate", "instances": ["xmp1", "xmp2"]},
        {"constraint": "Align", "line": "h_bottom", "instances": ["xmp1", "xmp2"]},
        {"constraint": "Boundary", "subcircuit": name, "max_height": 1.26}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=6, log_level='DEBUG')

    # variants = [fname.name for fname in (run_dir/'3_pnr'/'Results').iterdir()
    # if fname.name.startswith(name.upper()) and fname.name.endswith('.scaled_placement_verilog.json')]
    num_seq_pairs = _count_pattern(name.upper() + " sa_print_seq_pair")
    assert num_seq_pairs == 4, f'4 seq pairs expected but only {num_seq_pairs} seq pairs generated'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason="For next PR")
def test_enumerate_2():
    ''' Test SP enumerator in placement. Four devices can be permutated in two rows in 4! ways '''
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vi vo vccx vssx
        mp0 vo v1 vssx vccx p w=360e-9 m=1 nf=2
        mp1 v1 v2 vssx vccx p w=360e-9 m=1 nf=2
        mp2 v2 v3 vssx vccx p w=360e-9 m=1 nf=2
        mp3 v3 vi vssx vccx p w=360e-9 m=1 nf=2
        .ends
        """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]},
        {"constraint": "SameTemplate", "instances": ["mp0", "mp1", "mp2", "mp3"]},
        {"constraint": "NetPriority", "nets": ["v3"], "weight": 16},
        {"constraint": "NetPriority", "nets": ["v2"], "weight": 8},
        {"constraint": "NetPriority", "nets": ["v1"], "weight": 4},
        {"constraint": "NetPriority", "nets": ["vo"], "weight": 2},
        {"constraint": "NetPriority", "nets": ["vi"], "weight": 1},
        {"constraint": "PortLocation", "ports": ["v1"], "location": "RC"},
        {"constraint": "Boundary", "subcircuit": name, "max_height": 2.52, "max_width": 1.296}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=30, log_level='DEBUG')

    # variants = [fname.name for fname in (run_dir/'3_pnr'/'Results').iterdir()
    #   if fname.name.startswith(name.upper()) and fname.name.endswith('.scaled_placement_verilog.json')]
    num_seq_pairs = _count_pattern(name.upper() + " sa_print_seq_pair")
    assert num_seq_pairs == 576, f'576 seq pairs expected but only {num_seq_pairs} seq pairs generated'
    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_missing_power_port():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=8
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=6
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=16
        .ends {name}
        """)
    constraints = [{"constraint": "PowerPorts", "ports": ["vccxx"]}]
    example = build_example(name, netlist, constraints)
    try:
        run_example(example)
    except BaseException:
        assert False, 'This should not happen'
