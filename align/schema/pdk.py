from typing import List, Union, Dict, Optional
from align.schema import schema
from pydantic import validator, ValidationError, Field


class ParasiticValues(schema.BaseModel):
    mean: int = 0
    min: int = 0
    max: int = 0


class Layer(schema.BaseModel):
    name: str
    gds_layer_number: int
    gds_data_type: Optional[Dict[str, int]] = Field(default_factory=lambda: {"draw": 0})


class LayerMetal(Layer):

    direction: str

    min_length: int
    max_length: Optional[int]
    min_end_to_end: int

    offset: int
    width: Union[int, List[int]]
    space: Union[int, List[int]]
    color: Optional[List[str]]

    stop_pitch: int
    stop_point: int
    stop_offset: int

    unit_c: Optional[Dict[int, ParasiticValues]]
    unit_r: Optional[Dict[int, ParasiticValues]]
    unit_cc: Optional[Dict[int, ParasiticValues]]

    @validator('direction')
    def _validate_direction(cls, v):
        if v not in ['h', 'v']:
            raise ValueError('Direction value should be h or v')
        return v

    @validator('name')
    def _validate_name(cls, v):
        if not v.startswith('M'):
            raise ValueError('Metal layer name should start with M')
        return v

    @validator('min_length', 'min_end_to_end', 'width', 'space',
               'stop_pitch', 'stop_point')
    def _validate_positive(cls, v):
        if type(v) is list:
            if min(v) <= 0:
                raise ValueError('Values should be positive')
        else:
            if v <= 0:
                raise ValueError('Value should be positive')
        return v

    @validator('stop_offset')
    def _validate_non_negative(cls, v):
        if type(v) is list:
            if min(v) < 0:
                raise ValueError('Values should be non-negative')
        else:
            if v < 0:
                raise ValueError('Value should be non-negative')
        return v

    @validator('space')
    def _validate_width(cls, v, values):
        if type(v) is list:
            if len(v) != len(values['width']):
                raise ValueError('Width and space length should match')
        return v


class LayerVia(Layer):
    # Option #1: Specify list of options WxH  => specify in add via
    # Option #2: Specify option per metal combination m1_w x m2_w  => via_x
    # Option #3: Specify option per metal combination m1_w_c x m2_w_c  => via_1, via_2, via_3
    pass


class PDK(schema.BaseModel):
    name: str
    layers: List[Union[LayerMetal, LayerVia]]
    scale_factor: int = 1
