import logging
from . import types

from .types import Dict, Optional, List

logger = logging.getLogger(__name__)

class Model(types.BaseModel):
    '''
    Model creation class
    '''

    name : str                 # Model Name
    base : Optional[str]       # Model Base (for derived models)
    pins : Optional[List[str]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    prefix : Optional[str]     # Instance name prefix, optional

    def xyce(self):
        params = ' '.join(f'{k}={{{v}}}' for k, v in self.parameters.items())
        if self.base:
            return f'.MODEL {self.name} {self.base} {params}'
        else:
            return f'* .MODEL {self.name} ElementaryDevice({", ".join(self.pins)}) {params}'

    #
    # Private attributes affecting class behavior
    #

    @staticmethod
    def _get_base_model(library, name):
        return next((x for x in library if x.name == name), None)

    @property
    def bases(self):
        if self.base:
            return [self.base] + self._get_base_model(self.parent, self.base).bases
        else:
            return []

    @types.validator('name', allow_reuse=True)
    def name_check(cls, name):
        assert len(name) > 0, 'Model name cannot be an empty string'
        return name.upper()

    @types.validator('base', allow_reuse=True)
    def base_check(cls, base):
        library = cls._validator_ctx().parent
        assert library is not None, "Could not retrieve parent scope. Please register to library."
        base_ptr = cls._get_base_model(library, base.upper())
        assert base_ptr is not None, f"Could not find base model {base} in libary {library}"
        return base.upper()

    @types.validator('pins', always=True, allow_reuse=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert pins, 'Pins must be specified for base models. Did something go wrong in base?'
            assert len(pins) > 1, 'Instance must have at least two terminals'
            pins = [p.upper() for p in pins]
        elif pins:
            logger.error(f"Inheriting from {values['base'].name}. Cannot add pins")
            raise AssertionError(f"Inheriting from {values['base'].name}. Cannot add pins")
        else:
            pins = cls._get_base_model(cls._validator_ctx().parent, values['base']).pins.copy()
        return pins

    @types.validator('parameters', always=True, allow_reuse=True)
    def parameter_check(cls, parameters, values):
        parameters = {k.upper(): v.upper() for k, v in parameters.items()} if parameters else {}
        if 'base' in values and values['base']:
            x = cls._get_base_model(cls._validator_ctx().parent, values['base']).parameters.copy()
            x.update(parameters)
            parameters = x
        return parameters

    @types.validator('prefix', always=True, allow_reuse=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = cls._get_base_model(cls._validator_ctx().parent, values['base']).prefix
        return prefix

