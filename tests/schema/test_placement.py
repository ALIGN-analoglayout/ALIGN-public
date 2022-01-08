from align.schema import constraint
import pytest


def test_place_on_grid():
    os = constraint.OffsetsScalings()
    assert os.offsets == [0]
    assert os.scalings == [1]

    pg = constraint.PlaceOnGrid(direction='H', pitch=1000)
    os = pg.ored_terms[0]
    assert os.offsets == [0]
    assert os.scalings == [1]

    pg = constraint.PlaceOnGrid(direction='H', pitch=100, ored_terms=[constraint.OffsetsScalings(offsets=[10], scalings=[1])])
    os = pg.ored_terms[0]
    assert os.offsets == [10]
    assert os.scalings == [1]

    with pytest.raises(Exception):
        pg = constraint.PlaceOnGrid(direction='H', pitch=100, ored_terms=[constraint.OffsetsScalings(offsets=[100], scalings=[1])])
