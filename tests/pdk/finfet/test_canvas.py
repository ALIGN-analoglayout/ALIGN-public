import pathlib
from align.pdk.finfet import CanvasPDK
from align.primitive.default import DefaultCanvas
from align.cell_fabric import Pdk
import align.pdk.finfet
try:
    from .helper import *
except BaseException:
    from helper import *


layers_json = pathlib.Path(align.pdk.finfet.__file__).parent / 'layers.json'


def test_canvas_zero():
    c = CanvasPDK()


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

    compare_with_golden("test_canvas_1", c)


def test_canvas_two():

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


def test_canvas_three():

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

    export_to_viewer("test_canvas_3_c1", c1)
    export_to_viewer("test_canvas_3_c2", c2)

    d1 = {'bbox': c1.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c1.removeDuplicates(allow_opens=True)}
    d2 = {'bbox': c2.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c2.removeDuplicates(allow_opens=True)}

    assert d1 == d2
