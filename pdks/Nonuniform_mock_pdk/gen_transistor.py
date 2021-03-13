import os
import json
import pathlib
from canvas import NonuniformCanvas
from align.schema.transistor import Transistor


def mos(tx: Transistor):

    assert tx.nf % 2 == 0, f'Odd number of fingers are not allowed in this PDK.'

    # TODO: Below is an example of parameters to instantiate a PCELL
    # When flow is completed, instance is used to stamp the PCELLs where instantiated
    params = ' '.join([f'(\"dev_type\" \"string\" \"{tx.device_type}\")',
                       f'(\"vt_type\" \"string\" \"{tx.model_name}\")',
                       f'(\"nfin\" \"string\" \"{tx.nfin}\")'
                       f'(\"nf\" \"string\" \"{tx.nf}\")'
                       ])
    instance = {"library": "pdk_library", "cell": "pdk_mos", "view": "layout", "params": f'({params})'},

    c = NonuniformCanvas()

    if tx.device_type == 'stack':
        c.addWire(c.M1, 'S', 'S', 1,       (0, 1), (3, 3))
        c.addWire(c.M1, 'D', 'D', 1+tx.nf, (0, 1), (3, 3))
    else:
        for x in range(1, 2+tx.nf):
            p = 'D' if x % 2 == 0 else 'S'
            c.addWire(c.M1, p, p, x, (0, 1), (3, 3))

    for x in range(2, 1+tx.nf, 2):
        c.addWire(c.M1,  'G', 'G',  x, (4, 1), (5, 3))

    # for x in range(0, 8):
    #     c.addWire(c.M2,  None, None,  x, (0, 1), (6, 1))

    c.computeBbox()

    return {"bbox": c.bbox.toList(), "instance": instance, "terminals": c.terminals}


def test_one():
    tx = Transistor(device_type='stack',
                    nf=4,
                    nfin=4,
                    model_name='n')

    data = mos(tx)
    data['globalRoutes'] = []
    data['globalRouteGrid'] = []
    print(data)
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'test_transistor_one.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')


def test_two():

    tx = Transistor(device_type='parallel',
                    nf=4,
                    nfin=4,
                    model_name='p')
    data = mos(tx)
    data['globalRoutes'] = []
    data['globalRouteGrid'] = []
    print(data)
    with open(pathlib.Path(os.getenv('ALIGN_HOME'))/'Viewer'/'INPUT'/'test_transistor_two.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')
