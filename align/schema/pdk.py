from typing import List, Union, Dict, Optional, Tuple
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
    """
    Option #1: Specify a canonical via and adjust size via postprocessor (e.g self-aligned via)
               This is not sufficient for Analog Detailed Router

    Option #2: Specify a via for each lower and upper metal width combination
               This is not sufficient for Analog Detailed Router

    Option #3: Specify a canonical via and adjust size via postprocessor
               Specify the complete list of via width_x by width_y by color (auto-convert to ADR format)
               Optional: Specify via_patterns as needed for Intel ADR
               This seems to work
    """
    # Option #1: to demonstrate

    stack: Tuple[str, str]

    width_x: int
    width_y: int

    space_x: int
    space_y: int

    enc_l_x: Optional[int] = 0
    enc_l_y: Optional[int] = 0
    enc_h_x: Optional[int] = 0
    enc_h_y: Optional[int] = 0

    unit_r: Optional[Dict[int, ParasiticValues]]


class PDK(schema.BaseModel):
    name: str
    layers: Dict[str, Union[LayerMetal, LayerVia]] = Field(default_factory=lambda: {})
    scale_factor: int = 1

    def add_layer(self, layer):
        assert layer.name not in self.layers
        self.layers[layer.name] = layer

    @validator('layers')
    def _validate_stack_exists(cls, v):
        # TODO: For each via, check metal stack exists and metals are in orthogonal direction
        return v
