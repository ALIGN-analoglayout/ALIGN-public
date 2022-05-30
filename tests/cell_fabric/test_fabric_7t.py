
import json
import pathlib

import fabric_7t
from align.cell_fabric.transformation import Transformation

mydir = pathlib.Path(__file__).resolve().parent

def test_nunit_no_duplicates_7t():
    c = fabric_7t.Canvas()

    for (x,y) in ( (x,y) for x in range(4) for y in range(2)):

        c.pushTr( Transformation(x*c.unitCellWidth, y*c.unitCellHeight))

        if x % 2 != 0:
            c.hitTopTr( Transformation(1*c.unitCellWidth, 0*c.unitCellHeight, -1, 1))

        if y % 2 != 0:
            c.hitTopTr( Transformation(0*c.unitCellWidth, 1*c.unitCellHeight, 1, -1))

        c.nunit()
        c.popTr()

    fn = "__json_7t_nunit"
    with open( mydir / (fn + "_cand"), "wt") as fp:
        data = c.writeJSON( fp)

#    assert len(c.rd.opens) == 0
    assert len(c.rd.shorts) == 0

    with open( mydir / (fn + "_gold"), "rt") as fp:
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

    fn = "__json_7t_nunit_1x1"
    with open( mydir / (fn + "_cand"), "wt") as fp:
        data = c.writeJSON( fp)

#    assert len(c.rd.opens) == 0
    assert len(c.rd.shorts) == 0

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

        assert data == data2
