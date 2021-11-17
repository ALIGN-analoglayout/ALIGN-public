from align.schema.placement import OffsetsScalings, PlacementGrid


def test_offsets_scalings():
    os = OffsetsScalings()
    print(os)
    assert os.offsets == [0]
    assert os.scalings == [1]


def test_placement_grid():
    pg = PlacementGrid(direction='H', pitch=0)
    print(pg)
    os = pg.ored_terms[0]
    assert os.offsets == [0]
