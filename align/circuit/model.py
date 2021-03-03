import pydantic
import logging

from typing import Dict, ClassVar, Optional, List

logger = logging.getLogger(__name__)

class Model(pydantic.BaseModel):
    '''
    Model creation class

    This class is responsible for creating (and registering)
    new device types for a given PDK

    This class may be used in one of two ways:

    Mode1: To define base models (eg. PMOS, NMOS)
    :param name: Name of base model (eg. PMOS)
        common names: PMOS, NMOS, RES, CAP, IND
    :param pins: List of pins (eg. ['D', 'G', 'S', 'B']),
        must have at least two pins
    :param parameters: Dictionary of parameters (eg. {'param': 1.0}),
        optional
    :param prefix: Instance name prefix (eg. 'M' for transistor),
        optional

    Mode2: To define derived models (SPICE .MODEL)
    :param name: Name of new model (eg. PMOS_RVT)
    :param base: Library element to use as base (eg. PMOS)
    :param parameters: Dictionary of parameters (eg. {param: 1.0}),
        optional
        IMPORTANT: Must be a subset of base parameters if specified
    :param prefix: Instance name prefix (eg. M for transistor),
        assumed to be the same as base if not specified
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

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False

    def __call__(self, name, *pins, **parameters):
        assert len(pins) == len(self.pins), \
                f"Model {self.name} has {len(self.pins)} pins {self.pins}. " \
                + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}."
        pins = {pin: net.upper() for pin, net in zip(self.pins, pins)}

        return instance.Instance(
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

    @pydantic.validator('name', allow_reuse=True)
    def name_check(cls, name):
        assert len(name) > 0, 'Model name cannot be an empty string'
        return name.upper()

    @pydantic.validator('pins', always=True, allow_reuse=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert pins, 'Pins must be specified for base models. Did something go wrong in base?'
            assert len(pins) > 1, 'Instance must have at least two terminals'
            pins = [p.upper() for p in pins]
        elif pins:
            logger.error(f"Inheriting from {values['base'].name}. Cannot add pins")
            raise AssertionError(f"Inheriting from {values['base'].name}. Cannot add pins")
        else:
            pins = values['base'].pins.copy()
        return pins

    @pydantic.validator('parameters', always=True, allow_reuse=True)
    def parameter_check(cls, parameters, values):
        parameters = {k.upper(): v.upper() for k, v in parameters.items()} if parameters else {}
        if 'base' in values and values['base']:
            x = values['base'].parameters.copy()
            x.update(parameters)
            parameters = x
        return parameters

    @pydantic.validator('prefix', always=True, allow_reuse=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = values['base'].prefix
        return prefix

Model.update_forward_refs()

from . import instance
