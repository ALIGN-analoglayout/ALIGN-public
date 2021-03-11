from . import types
from .types import Union, Dict, Optional

import logging
logger = logging.getLogger(__name__)

class Instance(types.BaseModel):

    model: "Union[Model, SubCircuit]"
    name: str
    pins : Dict[str, str]
    parameters : Optional[Dict[str, str]]

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}={{{y}}}' for x, y in self.parameters.items())

    #
    # Private attributes affecting class behavior
    #

    @types.validator('name', allow_reuse=True)
    def name_complies_with_model(cls, name, values):
        name = name.upper()
        assert 'model' in values, 'Cannot run check without model definition'
        if values['model'].prefix and not name.startswith(values['model'].prefix):
            logger.error(f"{name} does not start with {values['model'].prefix}")
            raise AssertionError(f"{name} does not start with {values['model'].prefix}")
        return name

    @types.validator('pins', allow_reuse=True)
    def pins_comply_with_model(cls, pins, values):
        pins = {k.upper(): v.upper() for k, v in pins.items()}
        assert 'model' in values, 'Cannot run check without model definition'
        assert set(pins.keys()) == set(values['model'].pins)
        return pins

    @types.validator('parameters', allow_reuse=True, always=True)
    def parameters_comply_with_model(cls, parameters, values):
        assert 'model' in values, 'Cannot run check without model definition'
        if parameters:
            parameters = {k.upper(): v.upper() for k, v in parameters.items()}
            assert values['model'].parameters and set(parameters.keys()).issubset(values['model'].parameters.keys()), \
                f"{self.__class__.__name__} parameters must be a subset of {values['model'].__class__.__name__} parameters"
            parameters = {k: parameters[k] if k in parameters else v \
                for k, v in values['model'].parameters.items()}
        elif values['model'].parameters:
            parameters = values['model'].parameters.copy()
        return parameters

from .model import Model
from .subcircuit import SubCircuit
Instance.update_forward_refs()