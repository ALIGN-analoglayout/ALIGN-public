import json
import pathlib
from align.cell_fabric import Canvas, Wire, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent


def test_one():
    c = Canvas()

    c.pdk = {'M1': {'MaxL': None}, 'M2': {'MaxL': 10000}}

    m1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                       clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                       spg=EnclosureGrid(pitch=720, stoppoint=360)))

    m2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                       clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=5),
                       spg=EnclosureGrid(pitch=720, stoppoint=360)))

    # These three should be merged
    c.addWire(m1, 'a', 0, (0, 1), (3, 3))
    c.addWire(m1, 'a', 0, (4, 1), (5, 3))
    c.addWire(m1, 'a', 0, (6, 1), (50, 3))

    # Only the first two should be merged
    c.addWire(m2, 'a', 1, (0, 1), (3, 3))
    c.addWire(m2, 'a', 1, (4, 1), (5, 3))
    c.addWire(m2, 'a', 1, (6, 1), (50, 3))

    new_terminals = c.removeDuplicates(allow_opens=True)
    print('OLD:', new_terminals)
    c.join_wires(m1)
    c.join_wires(m2)
    new_terminals = c.removeDuplicates(allow_opens=True)
    print('NEW:', new_terminals)

    c.computeBbox()

    fn = "__json_join_wires_one"

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.removeDuplicates(allow_opens=True)}

    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps( data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_two():
    c = Canvas()

    c.pdk = {'M1': {'MaxL': None}, 'M2': {'MaxL': 10000}}

    m1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid(pitch=720, stoppoint=360)))

    # None of the below should merge
    c.addWire(m1, 'a',  1, (0, 1), (1, 3))
    c.addWire(m1, 'b',  1, (2, 1), (3, 3))
    c.addWire(m1, 'a',  1, (4, 1), (5, 3))

    # Append different width
    c.terminals.append({'layer': 'M1', 'netName': 'a', 'rect': [540, 4680, 900, 5400], 'netType': 'drawing'})

    c.addWire(m1, None, 1, (8, 1), (9, 3))

    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)
    c.join_wires(m1)
    new_terminals = c.removeDuplicates(allow_opens=True)
    print('new:', new_terminals)

    c.computeBbox()

    fn = "__json_join_wires_two"

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.removeDuplicates(allow_opens=True)}

    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps( data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_three():
    c = Canvas()

    c.pdk = {'M1': {'MaxL': 5000}}

    m1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                       clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                       spg=EnclosureGrid(pitch=720, stoppoint=360)))

    # Below should be merged
    c.addWire(m1, 'a', 0, (0, 1), (3, 3))
    c.addWire(m1, 'a', 0, (4, 1), (5, 3))
    # Below should be merged (but not with above)
    c.addWire(m1, 'a', 0, (6, 1), (8, 3))
    c.addWire(m1, 'a', 0, (10, 1), (11, 3))

    c.addWire(m1, 'b', 0, (12, 1), (13, 3))
    c.addWire(m1, 'a', 0, (14, 1), (15, 3))

    new_terminals = c.removeDuplicates(allow_opens=True)
    print('OLD:', new_terminals)
    c.join_wires(m1)
    new_terminals = c.removeDuplicates(allow_opens=True)
    print('NEW:', new_terminals)

    c.computeBbox()

    fn = "__json_join_wires_three"

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.removeDuplicates(allow_opens=True)}

    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps( data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2

def test_four():
    c = Canvas()

    c.pdk = {'M1': {'MaxL': None}, 'M2': {'MaxL': 10000}}

    m1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid(pitch=720, stoppoint=360)))

    # Below wires on same centerline should not be merged
    c.addWire(m1, 'a',  1, (0, 1), (1, 3), netType="blockage")
    c.addWire(m1, 'a',  1, (2, 1), (3, 3), netType="blockage")
    c.addWire(m1, 'a',  2, (0, 1), (1, 3), netType="drawing")
    c.addWire(m1, 'a',  2, (2, 1), (3, 3), netType="pin")
    c.addWire(m1, 'a',  4, (0, 1), (1, 3), netType="drawing")
    c.addWire(m1, 'a',  4, (2, 1), (3, 3), netType="blockage")
    # Below wires on same centerline should be merged
    c.addWire(m1, 'a',  3, (0, 1), (1, 3), netType="drawing")
    c.addWire(m1, 'a',  3, (2, 1), (3, 3), netType="drawing")
    c.addWire(m1, 'a',  5, (0, 1), (1, 3), netType="pin")
    c.addWire(m1, 'a',  5, (2, 1), (3, 3), netType="pin")


    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)
    c.join_wires(m1)
    new_terminals = c.removeDuplicates(allow_opens=True)
    print('new:', new_terminals)

    c.computeBbox()

    fn = "__json_join_wires_four"

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.removeDuplicates(allow_opens=True)}

    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps( data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


if __name__ == "__main__":
    test_one()
    test_two()
    test_three()
    test_four()
