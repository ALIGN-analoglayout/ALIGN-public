
import json
from cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

def test_one():
    c = Canvas()

    m1 = c.addGen( Wire( nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid( width=320, pitch=720,
                                                      offset=2*720,
                                                      repeat=20),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720,
                                                      offset=720,
                                                      repeat=10),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))

    m3 = c.addGen( Wire( nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720,
                                                      offset=2*720,
                                                      repeat=20),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    v2 = c.addGen( Via( nm='v2', layer='via2', h_clg=m2.clg, v_clg=m3.clg))

    ch = 5
    for base in [0, ch]:
        c.addWire( m1, 'S', None, 0, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'S', None, 6, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'S', None, 12, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'S', None, 18, (base + 1,1), (base + ch + 1,-1))

        c.addWire( m1, 'DA', None, 2, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'DA', None, 20, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'DB', None, 8, (base + 1,1), (base + ch + 1,-1))
        c.addWire( m1, 'DB', None, 14, (base + 1,1), (base + ch + 1,-1))
    
        c.addWire( m2, 'GND', None, 0 + base, (0,1), (24,-1))
        c.addWireAndViaSet('S', None, m2, v1, 1 + base, [0, 6, 12, 18])
        c.addWireAndViaSet('DA', None, m2, v1, 2 + base, [2, 20])
        c.addWireAndViaSet('DB', None, m2, v1, 3 + base, [8, 14])

    c.addWireAndViaSet('S', None, m3, v2, 5, [1, ch + 1])
    c.addWireAndViaSet('DA', None, m3, v2, 4, [2, ch + 2])
    c.addWireAndViaSet('DB', None, m3, v2, 9, [3, ch + 3])

    print (c.terminals)

    c.computeBbox ()

    fn = "tests/__json_diff_pair"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    with open( fn + "_cand", "wt") as fp:
        fp.write (json.dumps (data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data2 = json.load( fp)

        assert data == data2
