import os
import json
import pathlib
from align.pdk.finfet import CanvasPDK
from align.primitive.default import DefaultCanvas
from align.cell_fabric import Pdk
import align.pdk.finfet

my_dir = pathlib.Path(__file__).resolve().parent

layers_json = pathlib.Path(align.pdk.finfet.__file__).parent / 'layers.json'


def test_canvas_one():

    c = CanvasPDK()

    for x in range(1, 4):
        c.addWire(c.m1, 'a', None, x, (1, -1), (6, 1))
        c.addWire(c.m3, 'a', None, x, (1, -1), (6, 1))
        c.addWire(c.m5, 'a', None, x, (1, -1), (6, 1))
    for y in range(0, 8):
        c.addWire(c.m2, 'a', None, y, (1, -1), (3, 1))
        c.addWire(c.m4, 'a', None, y, (1, -1), (3, 1))
        c.addWire(c.m6, 'a', None, y, (1, -1), (3, 1))
    c.addVia(c.v1, 'a', None, 1, 1)
    c.addVia(c.v2, 'a', None, 1, 2)
    c.addVia(c.v3, 'a', None, 1, 3)
    c.addVia(c.v4, 'a', None, 1, 4)
    c.addVia(c.v5, 'a', None, 1, 5)

    c.computeBbox()

    data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c.removeDuplicates(allow_opens=True)}

    fn = "test_canvas_1"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_canvas_drc():

    c1 = CanvasPDK()
    c1.addWire(c1.m1, 'a', None, 1, (1, -1), (6, 1))
    c1.addWire(c1.m2, 'a', None, 1, (1, -1), (3, 1))
    c1.addVia(c1.v1,  'a', None, 1, 1)
    c1.computeBbox()
    c1.gen_data(run_drc=True)
    assert c1.drc.num_errors == 0

    c1 = CanvasPDK()
    c1.addWire(c1.m1, 'a', None, 1, (1, -1), (6, 1))
    c1.addWire(c1.m1, 'a', None, 2, (1, -1), (6, 1))
    c1.addWire(c1.m2, 'a', None, 1, (1, -1), (3, 1))
    c1.addVia(c1.v1,  'a', None, 1, 1)
    c1.addVia(c1.v1,  'a', None, 2, 1)
    c1.computeBbox()
    c1.gen_data(run_drc=True)
    assert c1.drc.num_errors == 1, f'horizontal via spacing'

    c1 = CanvasPDK() # vertical via spacing
    c1.addWire(c1.m2, 'a', None, 1, (1, -1), (3, 1))
    c1.addWire(c1.m2, 'a', None, 2, (1, -1), (3, 1))
    c1.addWire(c1.m3, 'a', None, 1, (1, -1), (6, 1))
    c1.addVia(c1.v2,  'a', None, 1, 1)
    c1.addVia(c1.v2,  'a', None, 1, 2)
    c1.computeBbox()
    c1.gen_data(run_drc=True)
    assert c1.drc.num_errors == 1, f'vertical via spacing'


def test_canvas_backward():

    def _helper(c):
        c.addWire(c.m1, 'a', None, 1, (1, -1), (6, 1))
        c.addWire(c.m3, 'a', None, 2, (1, -1), (6, 1))
        c.addWire(c.m5, 'a', None, 3, (1, -1), (6, 1))
        c.addWire(c.m2, 'a', None, 1, (1, -1), (3, 1))
        c.addWire(c.m4, 'a', None, 2, (1, -1), (3, 1))
        c.addWire(c.m6, 'a', None, 3, (1, -1), (3, 1))
        c.addVia(c.v1, 'a', None, 1, 1)
        c.addVia(c.v2, 'a', None, 2, 1)
        c.addVia(c.v3, 'a', None, 2, 2)
        c.addVia(c.v4, 'a', None, 3, 2)
        c.addVia(c.v5, 'a', None, 3, 3)
        c.computeBbox()

    c1 = CanvasPDK()
    _helper(c1)
    c1.gen_data(run_drc=True)
    assert c1.drc.num_errors == 0

    c2 = DefaultCanvas(Pdk().load(layers_json))
    _helper(c2)
    c2.gen_data(run_drc=True)
    assert c2.drc.num_errors == 0

    d1 = {'bbox': c1.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c1.removeDuplicates(allow_opens=True)}
    d2 = {'bbox': c2.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c2.removeDuplicates(allow_opens=True)}

    # for viewing
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/'test_canvas_1.json', "wt") as fp:
            fp.write(json.dumps(d1, indent=2) + '\n')

        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/'test_canvas_2.json', "wt") as fp:
            fp.write(json.dumps(d2, indent=2) + '\n')

        with open(my_dir / "text_canvas_backward_d1_cand.json", "wt") as fp:
            fp.write(json.dumps(d1, indent=2) + '\n')

        with open(my_dir / "text_canvas_backward_d1_cand.json", "wt") as fp:
            fp.write(json.dumps(d2, indent=2) + '\n')

    assert d1 == d2
