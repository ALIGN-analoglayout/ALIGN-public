import logging
from . import types

from .types import Dict, Optional, List

logger = logging.getLogger(__name__)

class Model(types.BaseModel):
    '''
    Model creation class
    '''

    name : str                 # Model Name
    base : "Optional[Model]"   # Model Base (for derived models)
    pins : Optional[List[str]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    prefix : Optional[str]     # Instance name prefix, optional

    def xyce(self):
        params = ' '.join(f'{k}={{{v}}}' for k, v in self.parameters.items())
        if self.base:
            return f'.MODEL {self.name} {self.base.name} {params}'
        else:
            return f'* .MODEL {self.name} ElementaryDevice({", ".join(self.pins)}) {params}'

    #
    # Private attributes affecting class behavior
    #

    def __call__(self, name, *pins, **parameters):
        assert len(pins) == len(self.pins), \
                f"Model {self.name} has {len(self.pins)} pins {self.pins}. " \
                + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}."
        pins = {pin: net.upper() for pin, net in zip(self.pins, pins)}

        return Instance(
            model=self,
            name=name,
            pins=pins,
            parameters=parameters
        )

    @property
    def bases(self):
        if self.base:
            return [self.base.name] + self.base.bases
        else:
            return []

    @types.validator('name', allow_reuse=True)
    def name_check(cls, name):
        assert len(name) > 0, 'Model name cannot be an empty string'
        return name.upper()

    @types.validator('pins', always=True, allow_reuse=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert pins, 'Pins must be specified for base models. Did something go wrong in base?'
            assert len(pins) >= 1, 'Instance must have at least one terminals (e.g., dummies have one terminal)'
            pins = [p.upper() for p in pins]
        elif pins:
            logger.error(f"Inheriting from {values['base'].name}. Cannot add pins")
            raise AssertionError(f"Inheriting from {values['base'].name}. Cannot add pins")
        else:
            pins = values['base'].pins.copy()
        return pins

    @types.validator('parameters', always=True, allow_reuse=True)
    def parameter_check(cls, parameters, values):
        parameters = {k.upper(): v.upper() for k, v in parameters.items()} if parameters else {}
        if 'base' in values and values['base']:
            x = values['base'].parameters.copy()
            x.update(parameters)
            parameters = x
        return parameters

    @types.validator('prefix', always=True, allow_reuse=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = values['base'].prefix
        return prefix

Model.update_forward_refs()

from .instance import Instance
