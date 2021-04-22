import json
import pytest
import pathlib
from align.schema import ConstraintsPlacement
from pydantic import parse_obj_as


def test_one():
    const = json.loads("""\
{
    "constraints": [
      {
        "constraint": "alignment",
        "instances": ["i0"],
        "direction": "horizontal",
        "edge": "bottom"
      },
      {
        "constraint": "generator",
        "instances": ["i1", "i2"],
        "style": "cc"
      },
      {
        "constraint": "orientation",
        "instances": ["i2"],
        "flip_y": true
      },
      {
        "constraint": "boundary",
        "subcircuits": ["subcircuit_a"],
        "aspect_ratio_min": 0.3,
        "aspect_ratio_max": 0.6
      }
    ]
  }
""")
    placement_constraints = parse_obj_as(ConstraintsPlacement, const)
    print(placement_constraints.json())


def test_two():
    const = json.loads("""\
{
    "constraints": [
      {
        "constraint": "alignment",
        "instances": ["i0, i1"],
        "direction": "horizontal",
        "edge": "nowhere"
      },
      {
        "constraint": "orientation",
        "instances": ["i1"],
        "flip_y": true
      }
    ]
  }
""")
    with pytest.raises(Exception):
        placement_constraints = parse_obj_as(ConstraintsPlacement, const)
        print(placement_constraints.json())
