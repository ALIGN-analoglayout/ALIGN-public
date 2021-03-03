import pydantic
import logging

from typing import Dict, ClassVar, Optional, List

from . import library

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
    base : Optional[str]       # Model Base (for derived models)
    pins : Optional[List[str]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    prefix : Optional[str]     # Instance name prefix, optional

    #
    # Private attributes affecting class behavior
    #

    library : ClassVar[library.Library]
    _baseptr = pydantic.PrivateAttr()

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False

    def __init__(self, library = library.default, **data):
        self.__class__.library = library
        super().__init__(**data)
        self.__class__.library.update({self.name: self})
        if self.base:
            self._baseptr = library[self.base]

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
            return [self.base] + self._baseptr.bases
        else:
            return []

    @pydantic.validator('name', allow_reuse=True)
    def name_check(cls, name):
        assert len(name) > 0
        return name.upper()

    @pydantic.validator('base', allow_reuse=True)
    def base_check(cls, base, values):
        if base:
            base = base.upper()
            if base not in cls.library:
                logger.error(f'Could not find {base} in library')
                raise AssertionError(f'Could not find {base} in library')
        return base

    @pydantic.validator('pins', always=True, allow_reuse=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert len(pins) > 1, 'Instance must have at least two terminals'
            pins = [p.upper() for p in pins]
        elif pins:
            logger.error(f"Inheriting from {values['base'].name}. Cannot add pins")
            raise AssertionError(f"Inheriting from {values['base'].name}. Cannot add pins")
        else:
            pins = cls.library[values['base']].pins.copy()
        return pins

    @pydantic.validator('parameters', always=True, allow_reuse=True)
    def parameter_check(cls, parameters, values):
        parameters = {k.upper(): v.upper() for k, v in parameters.items()} if parameters else {}
        if 'base' in values and values['base']:
            x = cls.library[values['base']].parameters.copy()
            x.update(parameters)
            parameters = x
        return parameters

    @pydantic.validator('prefix', always=True, allow_reuse=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = cls.library[values['base']].prefix
        return prefix

from . import instance
