import pydantic

from typing import Union, Dict, ClassVar

from .model import Model
from .subcircuit import SubCircuit

class Instance(pydantic.BaseModel):

    model: Union[Model, SubCircuit]
    name: str
    pins : Dict[str, str]
    parameters : Dict[str, str]

    def json(self):
        return super().json(include=self.jsonfilter)

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}={{{y}}}' for x, y in self.parameters.items())

    #
    # Private attributes affecting class behavior
    #

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False

    jsonfilter: ClassVar[Dict] = {
        'model': {'name'},
        'name': ...,
        'pins' : ...,
        'parameters' : ...
    }

    @pydantic.validator('name')
    def name_complies_with_model(cls, name, values):
        name = name.upper()
        if values['model'].prefix and not name.startswith(values['model'].prefix):
            logger.error(f"{name} does not start with {values['model'].prefix}")
            raise AssertionError(f"{name} does not start with {values['model'].prefix}")
        return name

    @pydantic.validator('pins')
    def pins_comply_with_model(cls, pins, values):
        pins = {k.upper(): v.upper() for k, v in pins.items()}
        assert set(pins.keys()) == set(values['model'].pins)
        return pins

    @pydantic.validator('parameters')
    def parameters_comply_with_model(cls, parameters, values):
        parameters = {k.upper(): v.upper() for k, v in parameters.items()}
        assert set(parameters.keys()).issubset(values['model'].parameters.keys())
        parameters = {k: parameters[k] if k in parameters else v \
            for k, v in values['model'].parameters.items()}
        return parameters
