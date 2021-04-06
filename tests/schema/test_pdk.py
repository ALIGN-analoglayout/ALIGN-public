import pathlib
import json
import pytest
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

    pdk = PDK(
        name= "Mock FinFET technology with non-uniform metal grids", 
        layers={'M1': m1, 'M2': m2, 'V1': v1_set}
        )

    with open(my_dir/"test_pdk_one-cand.json", "wt") as fp:
        fp.write(json.dumps(pdk.dict(), indent=2) + '\n')


def test_two():
    # upper metal not found 
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
    v1 = LayerVia(
        name="V1",
        gds_layer_number=21,
        stack=('M1', 'M3'),
        width_x=600,
        width_y=500,
        space_x=100,
        space_y=100,
    )
    v1_set = LayerViaSet(name="V1", gds_layer_number=21, default_via=v1)
    with pytest.raises(Exception):
        pdk = PDK(name= "Mock", layers={'M1': m1, 'V1': v1_set})

    # lower metal not found 
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
    v1 = LayerVia(
        name="V1",
        gds_layer_number=21,
        stack=('M0', 'M1'),
        width_x=600,
        width_y=500,
        space_x=100,
        space_y=100,
    )
    v1_set = LayerViaSet(name="V1", gds_layer_number=21, default_via=v1)
    with pytest.raises(Exception):
        pdk = PDK(name= "Mock", layers={'M1': m1, 'V1': v1_set})

    # metals not orthogonal 
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
        direction="v",
        min_length=500,
        min_end_to_end=300,
        offset=0,
        width=[400, 500, 500, 600, 600, 500, 500],
        space=[300, 300, 400, 400, 400, 300, 300],
        stop_pitch=1000,
        stop_point=350,
        stop_offset=0,
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
    with pytest.raises(Exception):
        pdk = PDK(name= "Mock", layers={'M1': m1, 'M2': m2, 'V1': v1_set})
