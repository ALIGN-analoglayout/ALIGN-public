import os
import json
import pathlib
# from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid
import canvas

# mydir = pathlib.Path(__file__).resolve().parent


def test_canvas():

    c = canvas.NonuniformCanvas()

    for x in range(0, 7):
        c.addWire(c.M1, 'M1', None, x, (0, 1), (5, 3))
    for y in range(0, 8):
        c.addWire(c.M2, 'M2', None, y, (0, 1), (5, 3))
        c.addWire(c.M4, 'M4', None, y, (0, 1), (5, 3))
    for x in range(0, 5):
        c.addWire(c.M3, 'M3', None, x, (0, 1), (5, 3))
        c.addWire(c.M5, 'M5', None, x, (0, 1), (5, 3))

    c.computeBbox()

    print(c.terminals)

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.terminals}

    # for viewing
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'nonuniform_canvas.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')


test_canvas()