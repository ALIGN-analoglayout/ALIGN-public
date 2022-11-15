
from align.pnr.checker import _flatten_leaves, _check_place_on_grid
from align.schema.constraint import PlaceOnGrid, OffsetsScalings
import pytest


def test_flatten_leaves():
    placement = {
        "leaves": [
            {
                "abstract_name": "INV",
                "bbox": [0, 0, 3000, 5000],
                "concrete_name": "INV"
            }
        ],
        "modules": [
            {
                "abstract_name": "CKT_TOP",
                "bbox": [0, 0, 3000, 18900],
                "concrete_name": "CKT_TOP_0",
                "instances": [
                    {
                        "abstract_template_name": "INV",
                        "concrete_template_name": "INV",
                        "instance_name": "XI0",
                        "transformation": {"oX": 3000, "oY": 0, "sX": 1, "sY": 1}
                    },
                    {
                        "abstract_template_name": "CKT_MID",
                        "concrete_template_name": "CKT_MID_0",
                        "instance_name": "XI2",
                        "transformation": {"oX": 0, "oY": 5000, "sX": 1, "sY": 1}
                    }
                ]
            },
            {
                "abstract_name": "CKT_MID",
                "bbox": [0, 0, 3000, 5000],
                "concrete_name": "CKT_MID_0",
                "instances": [
                    {
                        "abstract_template_name": "INV",
                        "concrete_template_name": "INV",
                        "instance_name": "XI0",
                        "transformation": {"oX": 0, "oY": 5000, "sX": 1, "sY": -1}
                    }
                ]
            }
        ]
    }
    flat_leaves_gold = [
        {'concrete_name': 'INV', 'name': 'XI0', 'transformation': {'oX': 3000, 'oY': 0, 'sX': 1, 'sY': 1}},
        {'concrete_name': 'INV', 'name': 'XI2/XI0', 'transformation': {'oX': 0, 'oY': 10000, 'sX': 1, 'sY': -1}}
    ]

    placement['leaves'] = {x['concrete_name']: x for x in placement['leaves']}
    placement['modules'] = {x['concrete_name']: x for x in placement['modules']}
    flat_leaves = _flatten_leaves(placement, 'CKT_TOP_0')
    assert flat_leaves == flat_leaves_gold, 'Value does not match golden'


def test_check_place_on_grid():

    constraints = [
        PlaceOnGrid(direction='H', pitch=100, ored_terms=[OffsetsScalings(offsets=[50], scalings=[1])]).dict(),
        PlaceOnGrid(direction='V', pitch=20, ored_terms=[OffsetsScalings(offsets=[0, 10], scalings=[1])]).dict()
    ]

    # H and V pass
    leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 40, 'oY': 150, 'sX': 1, 'sY': 1}}
    _check_place_on_grid(flat_leaf, constraints)

    leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 50, 'oY': 150, 'sX': 1, 'sY': 1}}
    _check_place_on_grid(leaf, constraints)

    # H fail due to offset
    with pytest.raises(AssertionError) as exe:
        leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 0, 'oY': 0, 'sX': 1, 'sY': 1}}
        _check_place_on_grid(leaf, constraints)
    assert "does not satisfy" in str(exe.value)

    # H fail due to scaling
    with pytest.raises(AssertionError) as exe:
        leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 0, 'oY': 50, 'sX': 1, 'sY': -1}}
        _check_place_on_grid(leaf, constraints)
    assert "does not satisfy" in str(exe.value)

    # V fail due to offset
    with pytest.raises(AssertionError) as exe:
        leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 7, 'oY': 50, 'sX': 1, 'sY': 1}}
        _check_place_on_grid(leaf, constraints)
    assert "does not satisfy" in str(exe.value)

    # V fail due to scaling
    with pytest.raises(AssertionError) as exe:
        leaf = {'name': 'u0', 'concrete_name': 'CELL_0', 'transformation': {'oX': 0, 'oY': 50, 'sX': -1, 'sY': 1}}
        _check_place_on_grid(leaf, constraints)
    assert "does not satisfy" in str(exe.value)
