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
    """ Partially routed single net """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(10):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')
        if i not in [5]:
            cv.addWire(cv.m3, None,  i, (0, -1),  (15, 1), netType='blockage')
    for i in range(9, 14, 2):
        cv.addWire(cv.m2, 'S',  i, (1, -1),  (8, 1), netType='pin')
    for i in range(1, 4, 2):
        cv.addWire(cv.m2, 'S',  i, (3, -1),  (6, 1), netType='pin')
    run_postamble(name, cv, max_errors=0)


def test_ru_3():
    """ Partially routed single net with multiplier """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(10):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')
        if i not in [4, 5]:
            cv.addWire(cv.m3, None,  i, (0, -1),  (15, 1), netType='blockage')
    for i in range(9, 14, 2):
        cv.addWire(cv.m2, 'S',  i, (1, -1),  (8, 1), netType='pin')
    for i in range(1, 4, 2):
        cv.addWire(cv.m2, 'S',  i, (3, -1),  (6, 1), netType='pin')
    constraints = [{"constraint": "MultiConnection", "nets": ["S"], "multiplier": 2}]
    data = run_postamble(name, cv, max_errors=0, constraints=constraints)
    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    # Quantify route quality
    segment_count = 0
    center_lines = set()
    for term in cvr.terminals:
        assert term['layer'] != 'M5', 'Why use M5 but not M3?'
        if term['layer'] == 'M3' and 'netName' in term and term['netName'] is not None:
            center_lines.add((term['rect'][0]+term['rect'][2])//2)
            segment_count += 1
    assert len(center_lines) == 2, f'Two M3 tracks suffice to complete routing {len(center_lines)}'
    assert segment_count == 2, f'Two M3 segments suffice to complete routing {segment_count}'


def test_ru_4():
    """ Partially routed single net no blockages """
    name = get_test_id()
    cv = CanvasPDK()
    for i in range(10):
        cv.addWire(cv.m1, None,  i, (0, -1),  (15, 1), netType='blockage')
    for i in range(9, 14, 2):
        cv.addWire(cv.m2, 'S',  i, (1, -1),  (8, 1), netType='pin')
    for i in range(1, 4, 2):
        cv.addWire(cv.m2, 'S',  i, (3, -1),  (6, 1), netType='pin')
    constraints = [{"constraint": "MultiConnection", "nets": ["S"], "multiplier": 2}]
    data = run_postamble(name, cv, max_errors=0, constraints=constraints)
    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    # Quantify route quality
    segment_count = 0
    center_lines = set()
    for term in cvr.terminals:
        assert term['layer'] != 'M5', 'Why use M5 but not M3?'
        if term['layer'] == 'M3' and 'netName' in term and term['netName'] is not None:
            center_lines.add((term['rect'][0]+term['rect'][2])//2)
            segment_count += 1
    assert len(center_lines) == 2, f'Two M3 tracks suffice to complete routing {len(center_lines)}'
    assert segment_count == 2, f'Two M3 segments suffice to complete routing {segment_count}'


def test_ru_5():
    """ Partially routed common centroid """
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


def test_ru_6():
    """ Partially routed common centroid """
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


def test_ru_exclude_m1():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m2, 'A',  9, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  1, (1, -1),  (6, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 8*cv.pdk['M1']['Pitch'], 10*cv.pdk['M2']['Pitch']])

    data = run_postamble(name, cv, max_errors=0, constraints=[{
          "constraint": "Route",
          "min_layer": "M2",
          "max_layer": "M3",
          "customize": []
        }])

    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    for term in cvr.terminals:
        assert term['layer'] != 'M1', 'M1 excluded'


def test_ru_exclude_m3():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m2, 'A',  9, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  1, (1, -1),  (6, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 8*cv.pdk['M1']['Pitch'], 10*cv.pdk['M2']['Pitch']])

    data = run_postamble(name, cv, max_errors=0, constraints=[{
          "constraint": "Route",
          "min_layer": "M1",
          "max_layer": "M2",
          "customize": []
        }])

    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    for term in cvr.terminals:
        assert term['layer'] != 'M3', 'M3 excluded'


def test_ru_exclude_per_net():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m2, 'A',  9, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m2, 'A',  1, (1, -1),  (6, 1), netType='pin')

    cv.addWire(cv.m2, 'B',  9, (9, -1),  (14, 1), netType='pin')
    cv.addWire(cv.m2, 'B',  1, (9, -1),  (14, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 16*cv.pdk['M1']['Pitch'], 10*cv.pdk['M2']['Pitch']])

    data = run_postamble(name, cv, max_errors=0, constraints=[{
          "constraint": "Route",
          "min_layer": "M1",
          "max_layer": "M3",
          "customize": [{'nets': ["A"], 'min_layer': "M2", 'max_layer': "M3"},
                        {'nets': ["B"], 'min_layer': "M1", 'max_layer': "M2"}]
        }])

    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    for term in cvr.terminals:
        assert term['netName'] != "A" or term['layer'] != 'M1', 'M1 excluded for net A'
        assert term['netName'] != "B" or term['layer'] != 'M3', 'M3 excluded for net A'


def test_ru_allow_ports_on_excluded_layers():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m1, 'A',  1, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m1, 'B',  1, (9, -1),  (14, 1), netType='pin')

    cv.addWire(cv.m3, 'A',  9, (1, -1),  (6, 1), netType='pin')
    cv.addWire(cv.m3, 'B',  9, (9, -1),  (14, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 10*cv.pdk['M1']['Pitch'], 16*cv.pdk['M2']['Pitch']])

    run_postamble(name, cv, max_errors=0, constraints=[{
          "constraint": "Route",
          "min_layer": "M2",
          "max_layer": "M2"
        }])


def test_ru_staggered_m1():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m1, 'A',  3, (2, -1),  (7, 1),  netType='pin')
    cv.addWire(cv.m1, 'A',  5, (9, -1),  (14, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 8*cv.pdk['M1']['Pitch'], 16*cv.pdk['M2']['Pitch']])

    run_postamble(name, cv, max_errors=0)


def test_ru_no_extra_routing_on_m1():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m1, 'A',  3, (2, -1),  (7, 1),  netType='pin')
    cv.addWire(cv.m1, 'A',  3, (9, -1),  (14, 1), netType='pin')

    cv.bbox = transformation.Rect(*[0, 0, 8*cv.pdk['M1']['Pitch'], 16*cv.pdk['M2']['Pitch']])

    constraints = [{
        "constraint": "Route",
        "min_layer": "M2",
        "max_layer": "M3"
    }]

    data = run_postamble(name, cv, max_errors=0, constraints=constraints)

    cvr = CanvasPDK()
    cvr.terminals = data['terminals']
    cvr.removeDuplicates(allow_opens=True, silence_errors=True)
    found_m3 = False
    for term in cvr.terminals:
        if term['netName'] == "A" and term['layer'] == 'M3':
            found_m3 = True

    assert found_m3, "Need m3 to make the connection."
