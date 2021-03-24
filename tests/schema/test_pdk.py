import pathlib
import json
from align.schema.pdk import LayerMetal, LayerVia, LayerViaSet, PDK

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():
    m1 = LayerMetal(
        name="M1",
        gds_layer_number=1,
        direction="v",
        min_length=1000,
        min_end_to_end=400,
        offset=0,
        width=[600],
        space=[400],
        stop_pitch=1000,
        stop_point=200,
        stop_offset=0
    )
    m2 = LayerMetal(
        name="M2",
        gds_layer_number=2,
        direction="h",
        min_length=500,
        min_end_to_end=300,
        offset=0,
        width=[400, 500, 500, 600, 600, 500, 500],
        space=[300, 300, 400, 400, 400, 300, 300],
        stop_pitch=1000,
        stop_point=350,
        stop_offset=0,
    )
    m3 = LayerMetal(
        name="M3",
        gds_layer_number=3,
        direction="v",
        min_length=1000,
        min_end_to_end=400,
        offset=0,
        width=[800, 1000],
        space=[600, 600],
        color=["a", "b"],
        stop_pitch=1000,
        stop_point=500,
        stop_offset=0
    )
    m4 = LayerMetal(
        name="M4",
        gds_layer_number=4,
        direction="h",
        min_length=500,
        min_end_to_end=300,
        offset=0,
        width=[400, 500, 500, 600, 600, 500, 500],
        space=[300, 300, 400, 400, 400, 300, 300],
        stop_pitch=1000,
        stop_point=350,
        stop_offset=0,
    )
    m5 = LayerMetal(
        name="M5",
        gds_layer_number=5,
        direction="v",
        min_length=1000,
        min_end_to_end=400,
        offset=0,
        width=[800, 1000],
        space=[600, 600],
        color=["a", "b"],
        stop_pitch=1000,
        stop_point=500,
        stop_offset=0
    )

    v1 = LayerVia(
        name="V1",
        gds_layer_number=21,
        stack=('M1', 'M2'),
        width_x=600,
        width_y=500,
        space_x=100,
        space_y=100,
    )
    v1_set = LayerViaSet(name="V1", gds_layer_number=21, default_via=v1)

    pdk = PDK(name=
                   """Mock FinFET technology with non-uniform metal grids.\
This PDK is for development and not functional yet.\
This file is auto-generated using tests/schema/test_pdk.py""",
                   layers={'M1': m1, 'M2': m2, 'M3': m3, 'M4': m4, 'M5': m5,
                           'V1': v1_set})

    # pprint.pprint(pdk.dict())
    with open(my_dir/"layers.json", "wt") as fp:
        fp.write(json.dumps(pdk.dict(), indent=2) + '\n')
