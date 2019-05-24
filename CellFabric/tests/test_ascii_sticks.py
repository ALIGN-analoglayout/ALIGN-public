
import json
from cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid

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
        c.addWire( m1, 'a', None, i, (0,1), (4,-1)) 

    for i in [1,3,5]:
        c.addWire( m1, 'b', None, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +b======+=======*
                    b    
+a======+=======+   |
                    |
    +b======+=======/


""")


    print( c.terminals)

    c.computeBbox()

    fn = "tests/__json_via_set_m2_m3_sticks"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data2 = json.load( fp)

        assert data == data2
