from pydantic import validator, ValidationError, Field
from .types import BaseModel, Union, Optional, Literal, List
from typing import Dict


class ParasiticValues(BaseModel):
    mean: int = 0
    min: int = 0
    max: int = 0


class Layer(BaseModel):
    name: str
    gds_layer_number: int
    gds_data_type: Optional[Dict[str, int]] = Field(default_factory=lambda: {"draw": 0})


class LayerMetal(Layer):

    direction: Literal['h', 'v']

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

    @validator('name')
    def _validate_name(cls, v):
        assert v.startswith('M'), f'Metal layer name {v} should start with M'
        return v

    @validator('min_length', 'min_end_to_end', 'width', 'space', 'stop_pitch', 'stop_point')
    def _validate_positive(cls, v):
        if isinstance(v, List):
            assert min(v) > 0, f'Values {v} should be positive'
        else:
            assert v > 0, f'Value {v} should be positive'
        return v

    @validator('stop_offset')
    def _validate_non_negative(cls, v):
        if isinstance(v, List):
            assert min(v) >= 0, f'Values {v} should be non-negative'
        else:
            assert v >= 0, f'Value {v} should be positive'
        return v

    @validator('space')
    def _validate_width(cls, v, values):
        if isinstance(v, List):
            assert len(v) == len(values['width']), f'width and space length should match'
        return v


class LayerVia(Layer):

    class Config:
        allow_mutation = True

    stack: List[str]

    width_x: int
    width_y: int

    space_x: int
    space_y: int

    layer_l_width: Optional[List[int]] = None
    layer_l_enc_x: Optional[int] = 0
    layer_l_enc_y: Optional[int] = 0

    layer_h_width: Optional[List[int]] = None
    layer_h_enc_x: Optional[int] = 0
    layer_h_enc_x: Optional[int] = 0

    unit_r: Optional[Dict[int, ParasiticValues]]

    @validator('stack')
    def _validate_stack(cls, v):
        assert len(v) == 2
        return v


class PDK(BaseModel):

    class Config:
        allow_mutation = True

    name: str
    layers: Dict[str, Union[LayerMetal, LayerVia]] = Field(default_factory=lambda: {})
    scale_factor: int = 1

    @validator('layers')
    def _validate_via(cls, layers):
        for key, via in layers.items():
            if isinstance(via, LayerVia):
                ml, mh = via.stack
                assert ml in layers, f'Lower layer {ml} not found for {key} {layers.keys()}'
                assert mh in layers, f'Higher layer {mh} not found for {key}'
                assert layers[ml].direction != layers[mh].direction, f'Lower and higher layer directions are not orthogonal'

                if via.layer_l_width is None:
                    via.layer_l_width = layers[ml].width.copy()
                if via.layer_h_width is None:
                    via.layer_h_width = layers[mh].width.copy()
        return layers

    def add_layer(self, layer):
        assert layer.name not in self.layers
        self.layers[layer.name] = layer
