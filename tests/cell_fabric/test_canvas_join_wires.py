import json
import pathlib
from align.cell_fabric import Canvas, Wire, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent


def test_one():
    c = Canvas()

    c.pdk = {'M1': {'MaxL': None}, 'M2': {'MaxL': 10000}}

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid(pitch=720, stoppoint=360)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=5),
                         spg=EnclosureGrid(pitch=720, stoppoint=360)))

    c.addWire(c.M1, 'a', None, 0, (0, 1), (3, 3))
    c.addWire(c.M1, 'a', None, 0, (4, 1), (5, 3))
    c.addWire(c.M1, 'a', None, 0, (6, 1), (50, 3))

    c.addWire(c.M2, 'a', None, 1, (0, 1), (3, 3))
    c.addWire(c.M2, 'a', None, 1, (4, 1), (5, 3))
    c.addWire(c.M2, 'a', None, 1, (6, 1), (50, 3))

    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)
    c.join_wires('M1')
    c.join_wires('M2')
    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)

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

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid(pitch=720, stoppoint=360)))

    c.addWire(c.M1, 'a',  None, 1, (0, 1), (1, 3))
    c.addWire(c.M1, 'b',  None, 1, (2, 1), (3, 3))
    c.addWire(c.M1, 'a',  None, 1, (4, 1), (5, 3))
    c.addWire(c.M1, None, None, 1, (6, 1), (7, 3))
    c.addWire(c.M1, None, None, 1, (8, 1), (9, 3))

    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)
    c.join_wires('M1')
    new_terminals = c.removeDuplicates(allow_opens=True)
    print(new_terminals)

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


if __name__ == "__main__":
    test_one()
    test_two()
