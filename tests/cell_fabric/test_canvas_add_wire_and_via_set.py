
import json
import pathlib

from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent

def test_one():
    c = Canvas()

    m1 = c.addGen( Wire( nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=5),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))

    for i in [0,2,4]:
        c.addWire( m1, 'a', i, (0,1), (4,-1)) 

    for i in [1,3,5]:
        c.addWire( m1, 'b', i, (0,1), (4,-1)) 

    c.addWireAndViaSet( 'a', m2, v1, 2, [0, 2, 4])
    c.addWireAndViaSet( 'b', m2, v1, 1, [1, 3, 5])

    print( c.terminals)

    c.computeBbox()

    fn = "__json_via_set"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

        assert data == data2

def test_two():
    c = Canvas()

    m1 = c.addGen( Wire( nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=5),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))

    for i in [0,2,4]:
        c.addWire( m1, 'a', i, (0,1), (4,-1)) 

    for i in [1,3,5]:
        c.addWire( m1, 'b', i, (0,1), (4,-1)) 

    c.addWireAndViaSet( 'a', m2, v1, 2, [(0,0), (1,0), (2,0)])
    c.addWireAndViaSet( 'b', m2, v1, 1, [(0,1), (1,1), (2,1)])

    print( c.terminals)

    c.computeBbox()

    fn = "__json_via_set2"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

        assert data == data2

def test_m2_and_m3():
    c = Canvas()

    m1 = c.addGen( Wire( nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    m2 = c.addGen( Wire( nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=5),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    m3 = c.addGen( Wire( nm='m3', layer='M3', direction='v',
                         clg=UncoloredCenterLineGrid( width=400, pitch=720, repeat=2),
                         spg=EnclosureGrid( pitch=720, stoppoint=360)))

    v1 = c.addGen( Via( nm='v1', layer='via1', h_clg=m2.clg, v_clg=m1.clg))
    v2 = c.addGen( Via( nm='v2', layer='via2', h_clg=m2.clg, v_clg=m3.clg))

    for i in [0,2,4]:
        c.addWire( m1, 'a', i, (0,1), (4,-1)) 

    for i in [1,3,5]:
        c.addWire( m1, 'b', i, (0,1), (4,-1)) 

    c.addWireAndViaSet( 'b', m2, v1, 3, [(0,1), (1,1), (2,1)])
    c.addWireAndViaSet( 'a', m2, v1, 2, [(0,0), (1,0), (2,0)])
    c.addWireAndMultiViaSet( 'b', m2, 1, [(v1, [(0,1), (1,1)]), (v2, [(2,1)])])

    c.addWireAndViaSet( 'b', m3, v2, (2,1), [1,3])


    print( c.terminals)

    c.computeBbox()

    fn = "__json_via_set_m2_m3"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
#             'terminals' : c.terminals}
             'terminals' : c.removeDuplicates()}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

        assert data == data2
