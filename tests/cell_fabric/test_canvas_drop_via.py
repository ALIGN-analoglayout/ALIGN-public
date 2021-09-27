import os
import json
import pathlib
from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent

# removing test
def test_one():

    c = Canvas()

    c.pdk = {"M1": {"Direction": "V"},
             "M2": {"Direction": "H"},
             "M3": {"Direction": "H"},
             "V1": {"Stack": ["M1", "M2"],
                    "SpaceX": 400, "SpaceY": 500, "WidthX": 400, "WidthY": 300,
                    "VencA_L": 0, "VencA_H": 0, "VencP_L": 0, "VencP_H": 0},
             "V2": {"Stack": ["M2", "M3"],
                   "SpaceX": 400, "SpaceY": 500, "WidthX": 400, "WidthY": 300,
                   "VencA_L": 0, "VencA_H": 0, "VencP_L": 0, "VencP_H": 0}}

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800, repeat=2),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=900, repeat=5),
                         spg=EnclosureGrid(pitch=800, stoppoint=400)))

    c.M3 = c.addGen(Wire(nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800, repeat=2),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.V1 = c.addGen(Via(nm='v1', layer='V1', h_clg=c.M2.clg, v_clg=c.M1.clg,
                        WidthX=c.pdk['V1']['WidthX'],
                        WidthY=c.pdk['V1']['WidthY']))

    c.V2 = c.addGen(Via(nm='v2', layer='V2', h_clg=c.M2.clg, v_clg=c.M3.clg,
                        WidthX=c.pdk['V2']['WidthX'],
                        WidthY=c.pdk['V2']['WidthY']))

    for x in [1, 2, 3]:
        c.addWire(c.M1, 'a', x, (0, 1), (3, 3))
    for y in [1, 2, 3]:
        c.addWire(c.M2, 'a', y, (1, 1), (5, 3))
    for x in [4, 5, 6]:
        c.addWire(c.M3, 'a', x, (0, 1), (3, 3))

    c.drop_via(c.V1)
    c.drop_via(c.V2)
    c.computeBbox()

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.terminals}

    # for viewing
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'drop_via_one.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    fn = "__json_drop_via_one"
    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_two():

    c = Canvas()

    c.pdk = {"M1": {"Direction": "V"},
             "M2": {"Direction": "H"},
             "V1": {"Stack": ["M1", "M2"],
                    "SpaceX": 700, "SpaceY": 700, "WidthX": 400, "WidthY": 300,
                    "VencA_L": 50, "VencA_H": 50, "VencP_L": 0, "VencP_H": 0}}

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800, repeat=2),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=900, repeat=5),
                         spg=EnclosureGrid(pitch=800, stoppoint=400)))

    c.V1 = c.addGen(Via(nm='v1', layer='V1', h_clg=c.M2.clg, v_clg=c.M1.clg,
                        WidthX=c.pdk['V1']['WidthX'],
                        WidthY=c.pdk['V1']['WidthY']))

    # via existing
    c.addWire(c.M1, 'a', 1, (0, 1), (1, 3))
    c.addWire(c.M2, 'a', 1, (0, 1), (1, 3))
    c.addVia(c.V1, 'a', 1, 1)

    # SpaceY violation
    c.addWire(c.M1, 'a', 3, (0, 1), (2, 3))
    c.addWire(c.M2, 'a', 1, (2, 1), (3, 3))
    c.addWire(c.M2, 'a', 2, (2, 1), (3, 3))

    # SpaceX violation
    c.addWire(c.M1, 'a', 5, (0, 1), (2, 3))
    c.addWire(c.M1, 'a', 6, (0, 1), (2, 3))
    c.addWire(c.M2, 'a', 1, (4, 1), (6, 3))

    # enclosure violation
    c.terminals.append({"layer": "M1", "netName": "a", "rect": [6200, 750, 6600, 2250], "netType": "drawing"})
    c.terminals.append({"layer": "M2", "netName": "a", "rect": [6200, 1600, 7000, 2000], "netType": "drawing"})
    c.addWire(c.M2, 'a', 1, (7, 1), (8, 3))

    c.drop_via(c.V1)
    c.computeBbox()
    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.terminals}

    # for viewing
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'drop_via_two.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    fn = "__json_drop_via_two"
    with open(mydir / (fn + "_cand"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


if __name__ == "__main__":
    test_one()
    test_two()
