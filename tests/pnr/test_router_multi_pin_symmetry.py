from align.pdk.finfet import CanvasPDK
from .utils import get_test_id, run_postamble
from align.cell_fabric import transformation

PIN = 'pin'
BLK = 'blockage'
NUN = None


def check_symmetry(terminals, net_a, net_b, direction):
    terminals_a = list()
    terminals_b = list()
    if direction == 'V':
        lla, ura = 1, 3
        llo, uro = 0, 2
    else:
        lla, ura = 0, 2
        llo, uro = 1, 3

    for term in terminals:
        if term['netName'] and term['layer'].startswith('M'):
            if term['netName'] == net_a:
                terminals_a.append(term)
            elif term['netName'] == net_b:
                terminals_b.append(term)

    symmetry_lines = list()
    for term_a in terminals_a:
        candidates = list()
        rect_a = term_a['rect']
        for term_b in terminals_b:
            rect_b = term_b['rect']
            if term_a['layer'] != term_b['layer']:
                continue
            if rect_a[lla] == rect_b[lla] and rect_a[ura] == rect_b[ura] and rect_a[uro]-rect_a[llo] == rect_b[uro]-rect_b[llo]:
                candidates.append(rect_b)

        assert candidates, 'Symmetric pin not found'
        assert len(candidates) == 1, 'MULTIPLE CANDIDATES!!!'
        rect_b = candidates[0]
        line = (rect_a[llo] + rect_a[uro] + rect_b[llo] + rect_b[uro]) // 2
        symmetry_lines.append(line)

    assert len(set(symmetry_lines)) == 1, f'Symmetry lines do not match {symmetry_lines}'


def test_ru_multi_symmetric():
    name = get_test_id()
    cv = CanvasPDK()

    cv.addWire(cv.m2, 'A', 1, (3, -1), (4, 1), netType=PIN)
    cv.addWire(cv.m2, 'A', 3, (3, -1), (4, 1), netType=PIN)
    cv.addWire(cv.m2, 'A', 6, (1, -1), (4, 1), netType=PIN)

    cv.addWire(cv.m2, 'B', 1, (6, -1), (7, 1), netType=PIN)
    cv.addWire(cv.m2, 'B', 3, (6, -1), (7, 1), netType=PIN)
    cv.addWire(cv.m2, 'B', 6, (6, -1), (9, 1), netType=PIN)

    cv.bbox = transformation.Rect(*[0, 0, 10*cv.pdk['M1']['Pitch'], 8*cv.pdk['M2']['Pitch']])

    check_symmetry(cv.terminals, 'A', 'B', 'V')

    data = run_postamble(name, cv, max_errors=10, constraints=[
        {"constraint": "Route", "min_layer": "M3", "max_layer": "M4"},
        {
            "constraint": "SymmetricNets",
            "net1": "A",
            "net2": "B",
            "pins1": ["ileaf/A__1", "ileaf/A__2", "ileaf/A__3"],
            "pins2": ["ileaf/B__1", "ileaf/B__2", "ileaf/B__3"],
            "direction": "V"
            }
    ])

    check_symmetry(data['terminals'], 'A', 'B', 'V')
