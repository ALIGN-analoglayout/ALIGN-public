import pathlib
import pprint
import json

from align.schema.pdk import LayerMetal, PDK

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():

    m1 = LayerMetal(
        name="M1",
        gds_layer_number=1,
        direction="v",
        min_length=1000,
        max_length=None,
        min_end_to_end=400,
        offset=0,
        width=[600],
        space=[400],
        stop_pitch=900,
        stop_point=100,
        stop_offset=0
    )

    m2 = LayerMetal(
        name="M2",
        gds_layer_number=2,
        direction="h",
        min_length=500,
        max_length=None,
        min_end_to_end=300,
        offset=0,
        width=[40, 45, 50, 60, 50, 45],
        space=[30, 30, 30, 30, 30, 30],
        color=["a", "b", "a", "b", "a", "b"],
        stop_pitch=1000,
        stop_point=300,
        stop_offset=0,
    )

    pdk = PDK(name="""Mock FinFET technology with non-uniform metal grids. 
    This PDK is for development and not functional yet.
    This file is auto-generated using tests/schema/test_pdk.py""",
              layers=[m1, m2])

    pprint.pprint(pdk.dict())
    with open(my_dir/"layers.json", "wt") as fp:
        fp.write(json.dumps(pdk.dict(), indent=2) + '\n')
