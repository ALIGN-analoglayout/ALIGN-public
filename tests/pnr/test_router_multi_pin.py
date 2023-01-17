from collections import defaultdict

from align.pdk.finfet import CanvasPDK
from .utils import get_test_id, run_postamble
from align.cell_fabric import gen_lef, transformation

PIN = 'pin'
BLK = 'blockage'
NUN = None


def extract_parasitics(data, nets):
    if isinstance(data, CanvasPDK):
        cv = data
    else:
        cv = CanvasPDK()
        cv.terminals = [term for term in data['terminals']]
    cv.gen_data()
    assert not cv.drc.errors
    total_cap = defaultdict(int)
    for component in cv.pex.components:
        name, pin_1, _, value = component
        for net in nets:
            if pin_1.upper().startswith(net) and name.startswith('c'):
                total_cap[net] += value
    results = dict()
    results['total_cap'] = total_cap
    return results


def test_ru_multi_0():
    name = get_test_id()

    # Routing problem
    def _routing_problem():
        cv = CanvasPDK()
        for x in [1, 3, 5]:
            cv.addWire(cv.m1, 'A', x, (1, -1), (3, 1), netType=PIN)
        for x in [7, 9, 11]:
            cv.addWire(cv.m1, 'A', x, (6, -1), (8, 1), netType=PIN)
        for x in range(6, 13):
            cv.addWire(cv.m1, NUN, x, (1, -1), (5, 1), netType=BLK)
        for x in range(7):
            cv.addWire(cv.m1, NUN, x, (4, -1), (8, 1), netType=BLK)
        return cv

    # A hand-crafted solution
    cv = _routing_problem()
    cv.addWire(cv.m2, 'A', 3, (1, -1), (7, 1), netType=PIN)
    cv.addWire(cv.m2, 'A', 6, (7, -1), (11, 1), netType=PIN)
    cv.addWire(cv.m3, 'A', 7, (3, -1), (6, 1), netType=PIN)
    cv.drop_via(cv.v1)
    cv.drop_via(cv.v2)

    data = run_postamble(name+'_GOLD', cv)
    res1 = extract_parasitics(cv, ['A'])

    # Routing problem
    cv = _routing_problem()
    data = run_postamble(name, cv, constraints=[{"constraint": "Route", "min_layer": "M2", "max_layer": "M4"}])
    res2 = extract_parasitics(data, ['A'])

    m3_segment = False
    for term in data['terminals']:
        if term['layer'] == 'M3':
            m3_segment = True

    assert m3_segment, 'Router did not respect min_layer'
    # assert res2['total_cap']['A'] <= res1['total_cap']['A']


def test_ru_multi_1():
    name = get_test_id()
    cv = CanvasPDK()

    for y in [0, 1, 3, 4, 5]:
        cv.addWire(cv.m2, NUN, y, (5, -1), (7, 1), netType=BLK)

    cv.addWire(cv.m2, NUN, 2, (11, -1), (13, 1), netType=BLK)

    for x in [1, 3, 9, 11, 13]:
        cv.addWire(cv.m1, 'A', x, (1, -1), (4, 1), netType=PIN)

    run_postamble(name, cv)


def test_ru_multi_2():
    name = get_test_id()
    cv = CanvasPDK()

    for y in range(5):
        cv.addWire(cv.m2, NUN, y, (5, -1), (7, 1), netType=BLK)

    for x in [1, 3, 9, 11, 13]:
        cv.addWire(cv.m1, 'A', x, (1, -1), (3, 1), netType=PIN)

    run_postamble(name, cv)


def test_ru_multi_3():
    name = get_test_id()
    cv = CanvasPDK()

    for y in range(6):
        cv.addWire(cv.m2, NUN, y, (5, -1), (7, 1), netType=BLK)

    for x in [1, 3, 9, 11, 13]:
        cv.addWire(cv.m1, 'A', x, (1, -1), (4, 1), netType=PIN)

    run_postamble(name, cv, constraints=[{"constraint": "Route", "min_layer": "M1", "max_layer": "M4"}])


def test_ru_multi_4():
    """ Partially routed single net """
    name = get_test_id()
    cv = CanvasPDK()

    for i in range(1, 4, 2):
        cv.addWire(cv.m2, 'S',  i, (3, -1),  (6, 1), netType='pin')

    for i in range(9, 14, 2):
        cv.addWire(cv.m2, 'S',  i, (1, -1),  (8, 1), netType='pin')

    cv.addWire(cv.m3, None,  3, (6, -1),  (8, 1), netType='blockage')
    cv.addWire(cv.m3, None,  4, (12, -1),  (13, 1), netType='blockage')

    data = run_postamble(name, cv, constraints=[{"constraint": "Route", "min_layer": "M2", "max_layer": "M3"}])

    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    # Quantify route quality
    segment_count = 0
    for term in cvr.terminals:
        if term['layer'] == 'M3' and 'netName' in term and term['netName'] == 'S':
            segment_count += 1
    assert segment_count == 1, f'One M3 segments suffice to complete routing {segment_count}'


def test_ru_multi_5():
    name = get_test_id()

    # Routing problem
    def _routing_problem():
        cv = CanvasPDK()
        cv.addWire(cv.m2, 'B',  13, (8, -1),  (12, 1), netType='pin')
        cv.addWire(cv.m2, 'B',  11, (2, -1),  (6, 1), netType='pin')
        cv.addWire(cv.m2, 'B',  3, (2, -1),  (6, 1), netType='pin')
        cv.addWire(cv.m2, 'B',  1, (8, -1),  (12, 1), netType='pin')
        return cv

    # A hand-crafted solution
    cv = _routing_problem()
    cv.addWire(cv.m2, 'B',  13, (7, -1),  (12, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  11, (2, -1),  (7, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  3, (2, -1),  (7, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  1, (7, -1),  (12, 1), netType='pin')
    cv.addWire(cv.m3, 'B', 7, (1, -1), (13, 1), netType='pin')
    cv.drop_via(cv.v2)

    data = run_postamble(name+'_GOLD', cv)
    res1 = extract_parasitics(cv, ['B'])

    # Routing problem
    cv = _routing_problem()
    data = run_postamble(name, cv, constraints=[{"constraint": "Route", "min_layer": "M3", "max_layer": "M4"}])
    res2 = extract_parasitics(data, ['B'])

    r = res2['total_cap']['B'] / res1['total_cap']['B']
    assert r <= 1.10, f'Capacitance is {r*100-100:.1f}% higher than optimal'
