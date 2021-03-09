import os
import json
import pathlib
from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent


def test_one():

    c = Canvas()

    c.pdk = {"M1": {"MaxL": None, "Direction": "V"},
             "M2": {"MaxL": 10000, "Direction": "H"},
             "V1": {"Stack": ["M1", "M2"],
                    "SpaceX": 400, "SpaceY": 500, "WidthX": 400, "WidthY": 300,
                    "VencA_L": 0, "VencA_H": 0, "VencP_L": 0, "VencP_H": 0}}

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800, repeat=2),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=900, repeat=5),
                         spg=EnclosureGrid(pitch=800, stoppoint=400)))

    c.V1 = c.addGen(Via(nm='v1', layer='V1', h_clg=c.M2.clg, v_clg=c.M1.clg,
                        WidthX=c.pdk['V1']['WidthX'],
                        WidthY=c.pdk['V1']['WidthY']))

    c.addWire(c.M1, 'a', None, 1, (0, 1), (3, 3))
    c.addWire(c.M2, 'a', None, 1, (0, 1), (3, 3))
    c.drop_via(c.V1)
    c.computeBbox()

    data_gold = {'bbox': [400, 450, 2800, 3150], 'globalRoutes': [], 'globalRouteGrid': [],
                 'terminals': [{'layer': 'M1', 'netName': 'a', 'rect': [600, 450, 1000, 3150]},
                               {'layer': 'M2', 'netName': 'a', 'rect': [400, 700, 2800, 1100]},
                               {'layer': 'V1', 'netName': 'a', 'rect': [600, 750, 1000, 1050]}]}

    data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [],
            'terminals': c.removeDuplicates(allow_opens=True)}
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'drop_via.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    assert data == data_gold


if __name__ == "__main__":
    test_one()