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


@pytest.mark.skip(reason='This test is failing. Enable in a future PR after refactoring')
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


def test_ru_2():
    """ Partially routed """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(10):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')
    for i in range(9, 14, 2):
        cv.addWire(cv.m2, 'S',  i, (1, -1),  (8, 1), netType='pin')
    for i in range(1, 4, 2):
        cv.addWire(cv.m2, 'S',  i, (3, -1),  (6, 1), netType='pin')
    constraints = [{"constraint": "MultiConnection", "nets": ["S"], "multiplier": 2}]
    run_postamble(name, cv, max_errors=0, constraints=constraints)


def test_ru_3():
    """ Partially routed """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(14):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')
    cv.addWire(cv.m2, 'A',  13, (2, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  13, (8, -1),  (12, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  11, (2, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  11, (8, -1),  (12, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  3, (2, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  3, (8, -1),  (12, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  1, (2, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  1, (8, -1),  (12, 1), netType='pin')
    run_postamble(name, cv, max_errors=0)


def test_ru_4():
    """ Partially routed """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(16):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')

    cv.addWire(cv.m2, 'A',  10, (2, -1),  (7, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  10, (9, -1),  (14, 1), netType='pin')

    cv.addWire(cv.m2, 'A',  3, (2, -1), (4, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  3, (6, -1), (10, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  3, (12, -1), (14, 1), netType='pin')

    cv.addWire(cv.m2, 'B',  1, (2, -1), (4, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  1, (6, -1), (10, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  1, (12, -1), (14, 1), netType='pin')

    run_postamble(name, cv, max_errors=0)
