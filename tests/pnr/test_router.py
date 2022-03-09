from align.pdk.finfet import CanvasPDK
from align.cell_fabric import transformation
from .utils import get_test_id, run_postamble
import pytest


def test_ru_zero():
    name = get_test_id()
    cv = CanvasPDK()
    cv.addWire(cv.m1, 'A', 1, (0, 1), (4, -1), netType='pin')
    cv.addWire(cv.m1, 'A', 4, (0, 1), (4, -1), netType='pin')
    cv.bbox = transformation.Rect(*[0, 0, 10*cv.pdk['M1']['Pitch'], 10*cv.pdk['M2']['Pitch']])
    run_postamble(name, cv, max_errors=0)


def test_ru_1():
    name = get_test_id()
    cv = CanvasPDK()
    cv.addWire(cv.m1, None, 1, (1, -1),  (19, 1))
    cv.addWire(cv.m1, 'A',  2, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m1, None, 3, (1, -1),  (6, 1))
    cv.addWire(cv.m1, 'A',  3, (10, -1), (19, 1), netType='pin')
    cv.addWire(cv.m1, None, 4, (1, -1),  (19, 1))
    cv.bbox = transformation.Rect(*[0, 0, 6*cv.pdk['M1']['Pitch'], 20*cv.pdk['M2']['Pitch']])
    run_postamble(name, cv, max_errors=0)
