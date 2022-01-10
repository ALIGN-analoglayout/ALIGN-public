
from align.schema.constraint import OffsetsScalings, PlaceOnGrid
from align.pnr.grid_constraints import lcm, check, merge

def test_lcm():
    assert lcm(2, 3) == 6
    assert lcm(2, 3, 4) == 12
    assert lcm(2, 3, 4, 5) == 60
    assert lcm(2, 3, 4, 5, 6) == 60

def test_A0():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=3, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])

    assert check(r0, 0, 1)
    assert not check(r0, 1,  1)
    assert check(r0, 2, 1)
    assert check(r1, 0, 1)
    assert not check(r1, 1,  1)
    assert check(r1, 3, 1)
    assert not check(r1, 0, -1)


def test_A1():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0, 1, 3], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1, -1])])
    r = merge(r0, r1)
    print(r)


def test_A2():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0], scalings=[-1]), OffsetsScalings(offsets=[1], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1, -1])])
    r = merge(r0, r1)
    print(r)


def test_A3():
    r0 = PlaceOnGrid(direction='H', pitch=4, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=6, ored_terms=[OffsetsScalings(offsets=[0, 1, 2], scalings=[1])])
    r = merge(r0, r1)
    print(r)


def test_A4():
    r0 = PlaceOnGrid(direction='H', pitch=2, ored_terms=[OffsetsScalings(offsets=[0], scalings=[1])])
    r1 = PlaceOnGrid(direction='H', pitch=3, ored_terms=[OffsetsScalings(offsets=[0, 1], scalings=[1])])
    r = merge(r0, r1)
    print(r)
