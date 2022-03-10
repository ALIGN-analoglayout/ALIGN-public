import os
import json
import pytest
import pathlib
from align.cell_fabric import Pdk, Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent


@pytest.fixture
def setup():

    p = Pdk()
    p.pdk = {
        "M1": {"Direction": "v", 'MaxL': None, 'MinL': 100, 'EndToEnd': 100},
        "M2": {"Direction": "h", 'MaxL': None, 'MinL': 100, 'EndToEnd': 100},
        "M3": {"Direction": "v", 'MaxL': None, 'MinL': 100, 'EndToEnd': 100},
        "V1": {"Stack": ["M1", "M2"], "SpaceX": 400, "SpaceY": 500, "WidthX": 400, "WidthY": 300,
               "VencA_L": 0, "VencA_H": 0, "VencP_L": 0, "VencP_H": 0},
        "V2": {"Stack": ["M2", "M3"], "SpaceX": 400, "SpaceY": 500, "WidthX": 400, "WidthY": 300,
               "VencA_L": 0, "VencA_H": 0, "VencP_L": 0, "VencP_H": 0}
    }

    c = Canvas(p)

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=900),
                         spg=EnclosureGrid(pitch=800, stoppoint=400)))

    c.M3 = c.addGen(Wire(nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800),
                         spg=EnclosureGrid(pitch=900, stoppoint=450)))

    c.V1 = c.addGen(Via(nm='v1', layer='V1', h_clg=c.M2.clg, v_clg=c.M1.clg,
                        WidthX=c.pdk['V1']['WidthX'],
                        WidthY=c.pdk['V1']['WidthY']))

    c.V2 = c.addGen(Via(nm='v2', layer='V2', h_clg=c.M2.clg, v_clg=c.M3.clg,
                        WidthX=c.pdk['V2']['WidthX'],
                        WidthY=c.pdk['V2']['WidthY']))

    return c


def test_one(setup):

    c = setup

    c.addWire(c.M1, 'a', 0, (0, -1), (3, 1))
    for i in range(4):
        c.addWire(c.M2, 'a', i, (0, -1), (3, 1))
    c.drop_via(c.V1)

    # for viewing
    c.computeBbox()
    data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c.terminals}
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'test_one.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    data = c.gen_data(run_pex=False)
    assert c.drc.num_errors == 0

    c.pdk['V1']['MaxAdjacentY'] = 3
    data = c.gen_data(run_pex=False)
    assert c.drc.num_errors == 1
    print('MaxAdjacentY is expected:', c.drc.errors)
