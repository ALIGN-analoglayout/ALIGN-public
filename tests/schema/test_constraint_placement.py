import json
import pytest
import pathlib
from align.schema import ConstraintsPlacement
from pydantic import parse_obj_as
import io

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():
    json_str = """\
{
    "constraints": [
      {
        "constraint_name": "alignment",
        "instances": ["i0"],
        "direction": "horizontal",
        "edge": "bottom"
      },
      {
        "constraint_name": "generator",
        "instances": ["i1", "i2"],
        "style": "cc"
      },
      {
        "constraint_name": "orientation",
        "instances": ["i2"],
        "flip_y": true
      },
      {
        "constraint_name": "boundary",
        "subcircuits": ["subcircuit_a"],
        "aspect_ratio_min": 0.3,
        "aspect_ratio_max": 0.6
      }
    ]
  }
"""   
    with io.StringIO( json_str) as fp:
        const = json.load(fp)
        placement_constraints = parse_obj_as(ConstraintsPlacement, const)
        print(placement_constraints.json())


def test_two():
    json_str = """\
{
    "constraints": [
      {
        "constraint_name": "alignment",
        "instances": ["i0, i1"],
        "direction": "horizontal",
        "edge": "nowhere"
      },
      {
        "constraint_name": "orientation",
        "instances": ["i1"],
        "flip_y": true
      }
    ]
  }
"""
    with io.StringIO( json_str) as fp:
        const = json.load(fp)
        with pytest.raises(Exception):
            placement_constraints = parse_obj_as(ConstraintsPlacement, const)
            print(placement_constraints.json())
