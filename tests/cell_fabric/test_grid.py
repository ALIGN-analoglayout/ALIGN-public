import pathlib
from align.cell_fabric import Canvas, Wire, UncoloredCenterLineGrid, EnclosureGrid

mydir = pathlib.Path(__file__).resolve().parent


def test_inverseBounds():

    c = Canvas()

    c.M1 = c.addGen(Wire(nm='m1', layer='M1', direction='v',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800),
                         spg=EnclosureGrid(pitch=800, stoppoint=200)))

    c.M2 = c.addGen(Wire(nm='m2', layer='M2', direction='h',
                         clg=UncoloredCenterLineGrid(width=400, pitch=800),
                         spg=EnclosureGrid(pitch=800, stoppoint=600)))

    # M1 is monotonic
    b, e = c.M1.spg.inverseBounds(600)
    assert b == e == (0, 3)

    b, e = c.M1.spg.inverseBounds(800)
    assert b == e == (1, 0)

    b, e = c.M1.spg.inverseBounds(900)
    assert b == (1, 0) and e == (1, 1)

    b, e = c.M1.spg.inverseBounds(1000)
    assert b == e == (1, 1)

    # M2 is not monotonic
    b, e = c.M2.spg.inverseBounds(600)
    assert b == e == (0, 1)

    b, e = c.M2.spg.inverseBounds(800)
    assert b == e == (1, 0)

    b, e = c.M2.spg.inverseBounds(900)
    assert b == (1, 0) and e == (1, 3)

    b, e = c.M2.spg.inverseBounds(1000)
    assert b == e == (1, 3)
