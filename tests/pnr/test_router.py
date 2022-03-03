from align.pdk.finfet import CanvasPDK
from align.cell_fabric import transformation
from .utils import get_test_id, run_postamble


def test_ru_zero():
    name = get_test_id()
    cv = CanvasPDK()
    cv.addWire(cv.m1, 'A', 1, (0, 1), (4, -1), netType='pin')
    cv.addWire(cv.m1, 'A', 4, (0, 1), (4, -1), netType='pin')
    cv.bbox = transformation.Rect(*[0, 0, 10*cv.pdk['M1']['Pitch'], 10*cv.pdk['M2']['Pitch']])
    run_postamble(name, cv, max_errors=0)
