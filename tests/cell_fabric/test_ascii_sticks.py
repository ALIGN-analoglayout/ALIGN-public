
import pytest
import json
import pathlib
from align.cell_fabric import Canvas, Wire, Via, UncoloredCenterLineGrid, EnclosureGrid
from itertools import chain, product

mydir = pathlib.Path(__file__).resolve().parent

def finish_test( c, fn):

    print( c.terminals)

    c.computeBbox()

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    assert len(c.rd.opens) == 0
    assert len(c.rd.shorts) == 0

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

        assert data == data2

@pytest.fixture
def setup():
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

    return (c, m1, v1, m2, v2, m3)


def test_m2_and_m3(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['b'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +b======+=======*
                    b    
+a======+=======+   |
                    |
    +b======+=======/


""")

    finish_test( c, "__json_via_set_m2_m3_sticks")

def test_m2_and_m3_infer(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], [None]), product( [1,3,5], [None])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +b======+=======*
                    |    
+a======+=======+   |
                    |
    +=======+=======/


""")

    finish_test( c, "__json_via_set_m2_m3_sticks")

def test_m2_and_m3_twochar(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['tw'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +tw=====+=======*
                    t    
+a======+=======+   w
                    |
    +tw=====+=======/


""")

    finish_test( c, "__json_via_set_m2_m3_sticks_twochar")

def test_m2_and_m3_unicode(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['b'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +b══════+═══════*
                    b    
+a══════+═══════+   ║
                    ║
    +b══════+═══════/


""")

    finish_test( c, "__json_via_set_m2_m3_sticks")

def test_m2_and_m3_unicode2(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['b'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +b══════*═══════+
            b    
+a══════+═══╬═══+
            ║
    +b══════*


""")

    finish_test( c, "__json_via_set_m2_m3_sticks2")

def test_m2_and_m3_resolve_names(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['b'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
    +═══════*═══════+
            ║
+═══════+═══╬═══+
            ║
    +═══════*


""")

    finish_test( c, "__json_via_set_m2_m3_sticks2")

def test_m2_and_m3_resolve_names_small(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in product( [0,2], [None]):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """


+a══════+




""")

    finish_test( c, "__json_via_set_m2_m3_sticks3")

def test_m2_and_m3_multicharskip(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['tw'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    # weird behavior, probably want to disallow
    c.asciiStickDiagram( v1, m2, v2, m3, """
    +tw=====+=======*
                    t    
+a======+=======+   |
                    w
    +t======+==w====/


""")

    finish_test( c, "__json_via_set_m2_m3_sticks_twochar")

def test_m2_and_m3_badchars(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['tw'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    with pytest.raises(AssertionError) as excinfo:
        c.asciiStickDiagram( v1, m2, v2, m3, """
 *  +tw=====+=======*
                    t    
+a======+=======+   w
                    |
    +tw=====+=======/


""")

    with pytest.raises(AssertionError) as excinfo:
        c.asciiStickDiagram( v1, m2, v2, m3, """
    +tw=====+=======*
 *                  t    
+a======+=======+   w
                    |
    +tw=====+=======/


""")



def test_m2_and_m3_different_pitch(setup):
    (c, m1, v1, m2, v2, m3) = setup

    for (i,nm) in chain( product( [0,2,4], ['a']), product( [1,3,5], ['b'])):
        c.addWire( m1, nm, i, (0,1), (4,-1)) 

    c.asciiStickDiagram( v1, m2, v2, m3, """
   +b====+=====*
               b
               |
+a====+=====+  |
               |
               |
   +b====+=====/



""", ypitch=3, xpitch=3)

    finish_test( c, "__json_via_set_m2_m3_sticks")

    
