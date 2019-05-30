
import json

import fabric_7t
from cell_fabric.transformation import Transformation

def test_nunit_no_duplicates():
    c = fabric_7t.Canvas()

    for (x,y) in ( (x,y) for x in range(4) for y in range(2)):

        c.pushTr( Transformation(x*c.unitCellWidth, y*c.unitCellHeight))

        if x % 2 != 0:
            c.hitTopTr( Transformation(1*c.unitCellWidth, 0*c.unitCellHeight, -1, 1))

        if y % 2 != 0:
            c.hitTopTr( Transformation(0*c.unitCellWidth, 1*c.unitCellHeight, 1, -1))
            
        c.nunit()
        c.popTr()

    c.computeBbox()

    fn = "tests/__json_7t_nunit"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

#    assert len(c.rd.opens) == 0
    assert len(c.rd.shorts) == 0

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data2 = json.load( fp)

        assert data == data2

def test_nunit_1x1():
    c = fabric_7t.Canvas()

    for (x,y) in ( (x,y) for x in range(1) for y in range(1)):

        c.pushTr( Transformation(x*c.unitCellWidth, y*c.unitCellHeight))

        if x % 2 != 0:
            c.hitTopTr( Transformation(1*c.unitCellWidth, 0*c.unitCellHeight, -1, 1))

        if y % 2 != 0:
            c.hitTopTr( Transformation(0*c.unitCellWidth, 1*c.unitCellHeight, 1, -1))
            
        c.nunit()
        c.popTr()

    c.computeBbox()

    fn = "tests/__json_7t_nunit_1x1"

    data = { 'bbox' : c.bbox.toList(),
             'globalRoutes' : [],
             'globalRouteGrid' : [],
             'terminals' : c.removeDuplicates()}

#    assert len(c.rd.opens) == 0
    assert len(c.rd.shorts) == 0

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data2 = json.load( fp)

        assert data == data2
