from pydantic import validator, ValidationError, Field
from .types import BaseModel, Union, Optional, Literal, List
from typing import Dict
import pathlib


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
    layer_h_enc_y: Optional[int] = 0

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


    def generate_adr_collaterals(self, write_path: pathlib.Path, x_grid: int, y_grid: int):

        with open(write_path/"adr_forbidden_patterns.txt", "wt") as fp:
            # TODO: Write rules for horizontal and vertical via spacing
            fp.write(f'\n')

        with open(write_path/"adr_options.txt", "wt") as fp:
            fp.write(f'Option name=gr_region_width_in_poly_pitches value={x_grid}\n')
            fp.write(f'Option name=gr_region_height_in_diff_pitches value={y_grid}\n')

        with open(write_path/"adr_design_rules.txt", "wt") as fp:
            for name, layer in self.layers.items():
                if isinstance(layer, LayerMetal):
                    fp.write(f'Rule name={name}_minete type=minete value={layer.min_end_to_end} layer={name}\n')
                    fp.write(f'Rule name={name}_minlength type=minlength value={layer.min_length} layer={name}\n')

        with open(write_path/"adr_metal_templates.txt", "wt") as fp:
            for name, layer in self.layers.items():
                if isinstance(layer, LayerMetal):
                    line = f'MetalTemplate layer={name} name={name}_template_0'
                    line += f' widths={",".join(str(i) for i in layer.width)}'
                    line += f' spaces={",".join(str(i) for i in layer.space)}'
                    if layer.color is not None and len(layer.color) > 0:
                        line += f' colors={",".join(str(i) for i in layer.color)}'
                    line += " stops=%s" % (",".join( str(i) for i in [layer.stop_pitch - 2*layer.stop_point, 2*layer.stop_point]))
                    line += '\n'
                    fp.write(line)

        def _via_string(via: LayerVia):

            via_str =  f'Generator name={via.name}_{via.width_x}_{via.width_y} {{ \n'
            via_str += f'  Layer1 value={via.stack[0]} {{\n'
            via_str += f'    x_coverage value={via.layer_l_enc_x}\n'
            via_str += f'    y_coverage value={via.layer_l_enc_y}\n'
            via_str += f'    widths value={",".join(str(i) for i in via.layer_l_width)}\n'
            via_str += f'  }}\n'
            via_str += f'  Layer2 value={via.stack[1]} {{\n'
            via_str += f'    x_coverage value={via.layer_h_enc_x}\n'
            via_str += f'    y_coverage value={via.layer_h_enc_y}\n'
            via_str += f'    widths value={",".join(str(i) for i in via.layer_h_width)}\n'
            via_str += f'  }}\n'
            via_str += f'  CutWidth value={via.width_x}\n'
            via_str += f'  CutHeight value={via.width_y}\n'
            via_str += f'  cutlayer value={via.name}\n'
            via_str += f'}}\n'

            return via_str

        with open(write_path/"adr_via_generators.txt", "wt") as fp:
            for name, layer in self.layers.items():
                if isinstance(layer, LayerVia):
                    via_str = _via_string(layer)
                    fp.write(via_str)
            fp.write(f'\n')

        with open(write_path/"adr_layers.txt", "wt") as fp:
            # TODO: Write out layers. write poly and diff if not exists using M1 and M2.
            fp.write(f'\n')
