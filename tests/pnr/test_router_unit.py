import pytest
import json
import pathlib
import os
import shutil
import datetime

from align.cell_fabric import pdk, gen_gds_json, gen_lef
from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid
from align.cell_fabric import transformation

import align

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path(os.environ['ALIGN_WORK_DIR']).resolve()
else:
    ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'


pdkdir = pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"

p = pdk.Pdk().load(pdkdir / 'layers.json')

def get_test_id():
    try:
        t = os.environ.get('PYTEST_CURRENT_TEST')
        t = t.split(' ')[0].split(':')[-1]
        t = t.replace('[', '_').replace(']', '').replace('-', '_')
        t = t[5:]
    except BaseException:
        t = 'debug'
    return t

@pytest.fixture
def setup():
    xpitch, ypitch = 80, 84

    m1_halfwidth = 16
    m1_minlength = 180
    m1_halfendtoend = 24

    m2_halfwidth = 16
    m2_minlength = 200
    m2_halfendtoend = 24

    c = Canvas()

    m1 = c.addGen( Wire( nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid( width=2*m1_halfwidth, pitch=xpitch),
                         spg=EnclosureGrid( pitch=ypitch, stoppoint=ypitch//2)))

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=2*m2_halfwidth, pitch=ypitch),
                         spg=EnclosureGrid( pitch=xpitch, stoppoint=xpitch//2)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))

    return (c, m1, v1, m2, xpitch, ypitch)


def run_postamble(nm, ctn, verilog_d, bbox, terminals, max_errors):
    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    primitives_d = { ctn : {'abstract_template_name': ctn, 'concrete_template_name': ctn}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    terminals.append(
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    )

    layout_d = {
        'bbox' : bbox,
        'globalRoutes' : [],
        'globalRouteGrid' : [],
        'terminals' : terminals
    }

    with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
        json.dump(layout_d, fp=fp, indent=2)

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p, mode='placement')

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn,
                     bodyswitch=1, blockM=0, p=p)

    os.chdir(run_dir)

    args = ['dummy_input_directory_can_be_anything', '-s', nm, '--flow_start', '3_pnr', '--skipGDS']
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f'No results for {nm}'

    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {nm} ({k})"
            assert v['errors'] <= max_errors, f"{nm} ({k}):Number of DRC errors: {str(v['errors'])}"


# We want this picture to make the following code
"""
    |   |   |   |               |   |   |   |
    A   B   C   D               A   B   C   D
    |   |   |   |               |   |   |   |
    |   |   |   |               |   |   |   |
"""

def run_horizontal_wire(nm, pins, setup, max_errors, extra_y=0):
    #==== Generate leaf cell =====
    (c, m1, v1, m2, xpitch, ypitch) = setup

    nx, ny = 20, 4
    bbox = [0, 0, nx * xpitch, (ny+extra_y) * ypitch]

    for i, actual in enumerate(pins):
        for j, off in enumerate( [1, nx-len(pins)]):
            net = actual + str(j)
            x = i + off
            c.addWire(m1, net, x, (0,1), (ny,-1), netType='pin')            

    c.bbox = transformation.Rect( *bbox)
    terminals = c.removeDuplicates()
    #==============================

    #==== Generate top-level netlist ====
    ctn = 'leaf'

    instance = {
        'instance_name': f'U0',
        'abstract_template_name': ctn,
        'fa_map': [ {'formal': actual + str(i), 'actual': actual} for actual in pins for i in range(2)]
    }

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': [instance],
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}
    #====================================

    run_postamble(nm, ctn, verilog_d, bbox, terminals, max_errors)


def run_vertical_wire(nm, pins, setup, max_errors, extra_x=0):
    #==== Generate leaf cell =====
    (c, m1, v1, m2, xpitch, ypitch) = setup

    nx, ny = 4, 30
    bbox = [0, 0, (nx+extra_x) * xpitch, ny * ypitch]

    for i, actual in enumerate(pins):
        for j, off in enumerate( [1, ny-len(pins)]):
            net = actual + str(j)
            y = i + off
            c.addWire(m2, net, y, (0,1), (nx,-1), netType='pin')            

    c.bbox = transformation.Rect( *bbox)
    terminals = c.removeDuplicates()
    #==============================

    #==== Generate top-level netlist ====
    ctn = 'leaf'

    instance = {
        'instance_name': f'U0',
        'abstract_template_name': ctn,
        'fa_map': [ {'formal': actual + str(i), 'actual': actual} for actual in pins for i in range(2)]
    }

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': [instance],
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}
    #====================================

    run_postamble(nm, ctn, verilog_d, bbox, terminals, max_errors)


def test_one_horizontal_wire(setup):
    run_horizontal_wire(get_test_id(), ["A"], setup, max_errors=0)

def test_two_horizontal_wires(setup):
    run_horizontal_wire(get_test_id(), ["A", "B"], setup, max_errors=0)

def test_three_horizontal_wires(setup):
    run_horizontal_wire(get_test_id(), ["A", "B", "C"], setup, max_errors=0)

def test_four_horizontal_wires(setup):
    run_horizontal_wire(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=1)

def test_four_horizontal_wires_extend(setup):
    run_horizontal_wire(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=0, extra_y=1)

def test_one_vertical_wire(setup):
    run_vertical_wire(get_test_id(), ["A"], setup, max_errors=0)

def test_two_vertical_wires(setup):
    run_vertical_wire(get_test_id(), ["A", "B"], setup, max_errors=0)

def test_three_vertical_wires(setup):
    run_vertical_wire(get_test_id(), ["A", "B", "C"], setup, max_errors=0)

def test_four_vertical_wires(setup):
    run_vertical_wire(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=0)



def run_horizontal_wire_with_obstacles(nm, pins, setup, max_errors, extra_y=0):
    #==== Generate leaf cell =====
    (c, m1, v1, m2, xpitch, ypitch) = setup

    nx, ny = 20, 4
    bbox = [0, 0, nx * xpitch, (ny+extra_y) * ypitch]

    for i, actual in enumerate(pins):
        for j, off in enumerate( [1, nx-len(pins)]):
            net = actual + str(j)
            x = i + off
            c.addWire(m1, net, x, (0,1), (ny,-1), netType='pin')            

    for i in range(1,ny):
        c.addWire(m2, f'obs_{i}', i, (nx//2-2,1), (nx//2+2,-1), netType='blockage')

    c.bbox = transformation.Rect( *bbox)
    terminals = c.removeDuplicates()
    #==============================

    #==== Generate top-level netlist ====
    ctn = 'leaf'

    instance = {
        'instance_name': f'U0',
        'abstract_template_name': ctn,
        'fa_map': [ {'formal': actual + str(i), 'actual': actual} for actual in pins for i in range(2)]
    }

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': [instance],
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}
    #====================================

    run_postamble(nm, ctn, verilog_d, bbox, terminals, max_errors)


def test_one_horizontal_wire_with_obstacles(setup):
    run_horizontal_wire_with_obstacles(get_test_id(), ["A"], setup, max_errors=0)

def test_two_horizontal_wires_with_obstacles(setup):
    run_horizontal_wire_with_obstacles(get_test_id(), ["A", "B"], setup, max_errors=0)

def test_three_horizontal_wires_with_obstacles(setup):
    run_horizontal_wire_with_obstacles(get_test_id(), ["A", "B", "C"], setup, max_errors=0)

def test_four_horizontal_wires_with_obstacles(setup):
    run_horizontal_wire_with_obstacles(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=1)

def test_four_horizontal_wires_with_obstacles_extend(setup):
    run_horizontal_wire_with_obstacles(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=0, extra_y=1)

def run_diagonal_wire(nm, pins, setup, max_errors):
    #==== Generate leaf cell =====
    (c, m1, v1, m2, xpitch, ypitch) = setup

    nx, ny = 20, 20
    bbox = [0, 0, nx * xpitch, ny * ypitch]

    for i, actual in enumerate(pins):
        for j, xoff in enumerate( [1, nx-len(pins)]):
            net = actual + str(j)
            x = i + xoff
            yoff = 0 if j == 0 else ny-4
            c.addWire(m1, net, x, (yoff+0,1), (yoff+4,-1), netType='pin')            

    c.bbox = transformation.Rect( *bbox)
    terminals = c.removeDuplicates()
    #==============================

    #==== Generate top-level netlist ====
    ctn = 'leaf'

    instance = {
        'instance_name': f'U0',
        'abstract_template_name': ctn,
        'fa_map': [ {'formal': actual + str(i), 'actual': actual} for actual in pins for i in range(2)]
    }

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': [instance],
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}
    #====================================

    run_postamble(nm, ctn, verilog_d, bbox, terminals, max_errors)

def test_four_diagonal_wires(setup):
    run_diagonal_wire(get_test_id(), ["A", "B", "C", "D"], setup, max_errors=0)

def xtest_ten_diagonal_wires(setup):
    run_diagonal_wire(get_test_id(), ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"], setup, max_errors=0)
