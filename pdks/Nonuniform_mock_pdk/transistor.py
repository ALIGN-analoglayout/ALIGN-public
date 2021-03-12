import os
import json
import pathlib
from canvas import NonuniformCanvas


def mos(*, dev_type, vt_type, nf, nfin):

    assert nf % 2 == 0, f'Odd number of fingers are not allowed.'

    params = ' '.join([f'(\"dev_type\" \"string\" \"{dev_type}\")',
                       f'(\"vt_type\" \"string\" \"{vt_type}\")',
                       f'(\"nfin\" \"string\" \"{nfin}\")'
                       f'(\"nf\" \"string\" \"{nf}\")'
                       ])

    instance = {"library": "pdk_library", "cell": "pdk_mos", "view": "layout", "params": f'({params})'},

    c = NonuniformCanvas()

    if dev_type == 'stack':
        c.addWire(c.M1, 'S', 'S', 1,    (0, 1), (3, 3))
        c.addWire(c.M1, 'D', 'D', 1+nf, (0, 1), (3, 3))
    elif dev_type == "parallel":
        for x in range(1, nf+2):
            p = 'D' if x % 2 == 0 else 'S'
            c.addWire(c.M1, p, p, x, (0, 1), (3, 3))
    else:
        assert False, f'Unknown device type {dev_type}'

    for x in range(2, nf+1, 2):
        c.addWire(c.M1,  'G', 'G',  x, (4, 1), (5, 3))

    # for x in range(0, 8):
    #     c.addWire(c.M2,  None, None,  x, (0, 1), (6, 1))

    c.computeBbox()

    return {"bbox": c.bbox.toList(), "instance": instance, "terminals": c.terminals}


def test_one():

    data = mos(dev_type="stack", vt_type="n", nf=6, nfin=4)
    data['globalRoutes'] = []
    data['globalRouteGrid'] = []
    print(data)
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'test_transistor_one.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')


def test_two():

    data = mos(dev_type="parallel", vt_type="n", nf=6, nfin=4)
    data['globalRoutes'] = []
    data['globalRouteGrid'] = []
    print(data)
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'test_transistor_two.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')
