import json
import pathlib

import fabric_gf

mydir = pathlib.Path(__file__).resolve().parent

def test_nunit():
    c = fabric_gf.CanvasNMOS()

    for (x,y) in ( (x,y) for x in range(2) for y in range(1)):
        c.nunit( x, y)

    c.computeBbox()

    fn = "__json_nunit"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.terminals}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

    assert data == data2

def test_nunit_no_duplicates_gf():
    c = fabric_gf.CanvasNMOS()

    for (x,y) in ( (x,y) for x in range(2) for y in range(1)):
        c.nunit( x, y)

    c.computeBbox()

    fn = "__json_nunit_no_duplicates"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

    assert data == data2

def test_cunit():
    c = fabric_gf.CanvasNMOS()

    for (x,y) in ( (x,y) for x in range(16) for y in range(4)):
        c.cunit( x, y)

    c.computeBbox()

    fn = "__json_cunit"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.terminals}

    with open( mydir / (fn + "_cand"), "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

    assert data == data2


