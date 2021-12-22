from align.schema import constraint


def test_place_on_grid():
    os = constraint.OffsetsScalings()
    assert os.offsets == [0]
    assert os.scalings == [1]

    pg = constraint.PlaceOnGrid(direction='H', pitch=1000)
    os = pg.ored_terms[0]
    assert os.offsets == [0]
    assert os.scalings == [1]
