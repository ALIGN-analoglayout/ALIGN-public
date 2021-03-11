from typing import List, Union, Dict
from align.schema import schema


class ParasiticValues(schema.BaseModel):
    mean: int = 0
    min: int = 0
    max: int = 0


class Layer(schema.BaseModel):
    name: str
    gds_layer_number: int
    gds_data_type: dict = {"draw": 0}


class LayerMetal(Layer):

    direction: str

    min_length: int
    max_length: Union[int, None] = None
    min_end_to_end: int

    offset: int
    width: Union[int, List[int]]
    space: Union[int, List[int]]
    color: Union[None, List[str]] = None

    stop_pitch: int
    stop_point: int
    stop_offset: int

    unit_c: Union[Dict[int, ParasiticValues], None] = None
    unit_r: Union[Dict[int, ParasiticValues], None] = None
    unit_cc: Union[Dict[int, ParasiticValues], None] = None


class LayerVia(Layer):
    # Option #1: Specify list of options WxH  => specify in add via
    # Option #2: Specify option per metal combination m1_w x m2_w  => via_x
    # Option #3: Specify option per metal combination m1_w_c x m2_w_c  => via_1, via_2, via_3
    pass


class PDK(schema.BaseModel):
    name: str
    layers: List[Union[LayerMetal, LayerVia]]
    scale_factor: int = 1
