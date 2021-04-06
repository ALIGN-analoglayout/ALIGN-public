import json
import pytest
import pathlib
from align.schema import ConstraintsPlacement
from pydantic import parse_obj_as


def test_one():
    json_str = """\
    {
      "constraints": [
        {
          "name": "align",
          "instances": ["i0", "i1"],
          "direction": "horizontal",
          "line": "bottom"
        },
        {
          "name": "generator",
          "instances": ["i1", "i2"],
          "style": "cc",
          "alias": "diffpair"
        },
        {
          "name": "mirror",
          "instances": ["i2"],
          "y_axis": true
        },
        {
          "name": "boundary",
          "aspect_ratio_min": 0.3,
          "aspect_ratio_max": 0.6
        }
      ]
    }
    """
    const = json.loads(json_str)
    placement_constraints = parse_obj_as(ConstraintsPlacement, const)


def test_two():
    json_str = """\
    {
      "constraints": [
        {
          "name": "align",
          "instances": ["i0, i1"],
          "direction": "horizontal",
          "line": "nowhere"
        },
        {
          "name": "orientation",
          "instances": ["i1"],
          "flip_y": true
        }
      ]
    }
    """
    const = json.loads(json_str)
    with pytest.raises(Exception):
        placement_constraints = parse_obj_as(ConstraintsPlacement, const)
        print(placement_constraints.json())
