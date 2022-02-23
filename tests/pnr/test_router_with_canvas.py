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

    m3 = c.addGen( Wire( nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid( width=2*m1_halfwidth, pitch=xpitch),
                         spg=EnclosureGrid( pitch=ypitch, stoppoint=ypitch//2)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))
    v2 = c.addGen( Via( nm='v2', layer='via2', h_clg=m2.clg, v_clg=m3.clg))

    return (c, m1, v1, m2, v2, m3, xpitch, ypitch)



def run_common(nm, pins, setup, max_errors):

    run_dir = ALIGN_WORK_DIR / f'{nm}_routing_unit_tests'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    instances = [
        {
            'instance_name': f'U0',
            'abstract_template_name': 'leaf',
            'fa_map': [ {'formal': actual + str(i), 'actual': actual} for actual in pins for i in range(2)]
        }
    ]

    topmodule = {
        'name': nm.upper(),
        'parameters': [],
        'instances': instances,
        'constraints': []
    }

    verilog_d = {'modules': [topmodule], 'global_signals': []}

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        json.dump(verilog_d, fp=fp, indent=2)

    # ==========================

    primitives_d = { 'leaf' : {'abstract_template_name': 'leaf', 'concrete_template_name': 'leaf'}}

    with (run_dir / '1_topology' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        json.dump(primitives_d, fp=fp, indent=2)


    (c, m1, v1, m2, v2, m3, xpitch, ypitch) = setup

    nx, ny = 20, 4
    bbox = [0, 0, nx * xpitch, ny * ypitch]

    # We want this picture to make the following code
    """
    |   |   |   |               |   |   |   |
    A   B   C   D               A   B   C   D
    |   |   |   |               |   |   |   |
    |   |   |   |               |   |   |   |
"""


    for i, actual in enumerate(pins):
        for j, off in enumerate( [1, nx-len(pins)]):
            net = actual + str(j)
            x = i + off
            c.addWire(m1, net, x, (0,1), (4,-1), netType='pin')            

    print(c.terminals)

    #c.computeBbox()
    c.bbox = transformation.Rect( *bbox)
    terminals = c.removeDuplicates()

    terminals.append(
        {
            "layer": "Nwell",
            "netName": None,
            "rect": bbox,
            "netType": "drawing"
        }
    )


    layout_d = {
        'bbox' : c.bbox.toList(),
        'globalRoutes' : [],
        'globalRouteGrid' : [],
        'terminals' : terminals
    }


    ctn = 'leaf'

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


def test_one_horizontal_wire_canvas(setup):
    run_common('one_horizontal_wire_canvas', ["A"], setup, max_errors=0)

def test_two_horizontal_wires_canvas(setup):
    run_common('two_horizontal_wires_canvas', ["A", "B"], setup, max_errors=0)

def test_three_horizontal_wires_canvas(setup):
    run_common('three_horizontal_wires_canvas', ["A", "B", "C"], setup, max_errors=0)

def test_four_horizontal_wires_canvas(setup):
    run_common('four_horizontal_wires_canvas', ["A", "B", "C", "D"], setup, max_errors=1)
