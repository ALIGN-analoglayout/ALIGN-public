import json
import pytest
import pathlib
from align.schema import ConstraintsPlacement
from pydantic import parse_obj_as

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():
    with open(my_dir/'constraint_placement_1.json', "rt") as fp:
        const = json.load(fp)
        placement_constraints = parse_obj_as(ConstraintsPlacement, const)
        print(placement_constraints.json())


def test_two():
    with open(my_dir/'constraint_placement_2.json', "rt") as fp:
        const = json.load(fp)
        with pytest.raises(Exception):
            placement_constraints = parse_obj_as(ConstraintsPlacement, const)
            print(placement_constraints.json())
