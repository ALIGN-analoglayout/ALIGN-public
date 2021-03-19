import os
import json
import pathlib
from . import canvas


def test_canvas():

    c = canvas.CanvasPDK()

    for x in range(0, 7):
        c.addWire(c.M1, 'a', None, x, (0, 1), (5, 3))
    for y in range(0, 8):
        c.addWire(c.M2, 'a', None, y, (0, 1), (5, 3))
        c.addWire(c.M4, 'a', None, y, (0, 1), (5, 3))
    for x in range(0, 5):
        c.addWire(c.M3, 'a', None, x, (0, 1), (5, 3))
        c.addWire(c.M5, 'a', None, x, (0, 1), (5, 3))

    for y in range(1, 2):
        for x in range(1, 4):
            c.addVia(c.V1, 'a', None, x, y)
            c.addVia(c.V2, 'a', None, x, y+1)
            c.addVia(c.V3, 'a', None, x, y+2)
            c.addVia(c.V4, 'a', None, x, y+3)

    c.computeBbox()

    data = {'bbox': c.bbox.toList(),
            'globalRoutes': [],
            'globalRouteGrid': [],
            'terminals': c.terminals}

    # for viewing
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'nonuniform_canvas.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')


test_canvas()
