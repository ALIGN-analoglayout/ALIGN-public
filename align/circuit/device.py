import pydantic
import logging

from typing import Dict, ClassVar, Union, Optional, List
from pydantic import StrictStr, StrictFloat, StrictInt, PrivateAttr, Field
ParamValue = Union[StrictFloat, StrictInt, StrictStr]

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
        must have at least one parameter to be meaningful
    :param prefix: Instance name prefix (eg. 'M' for transistor),
        optional

    Mode2: To define derived models (SPICE .MODEL)
    :param name: Name of new model (eg. PMOS_RVT)
    :param base: Library element to use as base (eg. PMOS)
    :param parameters: Dictionary of parameters (eg. {param: 1.0})
        IMPORTANT: Must be a subset of base parameters
    :param prefix: Instance name prefix (eg. M for transistor),
        assumed to be the same as base if not specified
    '''

    name : StrictStr
    base : Optional[StrictStr]       # Optional for Base Models
    pins : Optional[List[StrictStr]] # Optional when inheriting
    parameters : Dict[StrictStr, ParamValue]
    prefix : Optional[StrictStr]     # Always optional

    #
    # Private attributes affecting class behavior
    #

    library : ClassVar[Dict] = dict()

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        validate_all = True

    def __init__(self, **data):
        super().__init__(**data)
        self.__class__.library.update(
            {self.name: self}
        )

    def __call__(self, name, *pins, **parameters):
        return Device(
            model=self,
            library=self.library,
            name=name,
            pins=pins,
            parameters=parameters
        )

    @pydantic.validator('name')
    def name_check(cls, name):
        assert len(name) > 0
        return name

    @pydantic.validator('base', pre=True, always=True)
    def base_check(cls, base, values):
        if base and base not in cls.library:
            logger.error(f'Could not find {base} in library')
            raise AssertionError
        return base

    @pydantic.validator('pins', pre=True, always=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert len(pins) > 1, 'Device must have at least two terminals'
        elif pins:
            logger.error( f"Inheriting from {values['base'].name}. Cannot add pins" )
            raise AssertionError
        else:
            pins = cls.library[values['base']].pins.copy()
        return pins

    @pydantic.validator('parameters', pre=True, always=True)
    def parameter_check(cls, parameters, values):
        if 'base' not in values or not values['base']:
            assert len(parameters) > 0, 'Device must have at least one parameter'
        elif not set(parameters.keys()).issubset(cls.library[values['base']].parameters.keys()):
            logger.error(f"Inheriting from {base.name}. Cannot add new parameters")
            raise AssertionError
        else:
            parameters = {k: parameters[k] if k in parameters else v \
                for k, v in cls.library[values['base']].parameters.items()}
        return parameters

    @pydantic.validator('prefix', pre=True, always=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = cls.library[values['base']].prefix
        return prefix

class Device(pydantic.BaseModel):

    model: Model
    name: StrictStr
    pins : Dict[StrictStr, StrictStr]
    parameters : Dict[StrictStr, ParamValue]

    #
    # Private attributes affecting class behavior
    #

    library : ClassVar[Dict] = None

    def __init__(self, library=None, **data):
        assert library is not None
        self.__class__.library = library
        super().__init__(**data)
        self.__class__.library = None

    @pydantic.validator('name', pre=True)
    def name_complies_with_model(cls, name, values):
        if values['model'].prefix:
            if not name.startswith(values['model'].prefix):
                logger.error(f"{name} does not start with {values['model'].prefix}")
                raise AssertionError
        return name

    @pydantic.validator('pins', pre=True)
    def pins_comply_with_model(cls, pins, values):
        if isinstance(pins, dict):
            assert set(pins.keys()) == set(values['model'].pins)
        else:
            if len(pins) != len(values['model'].pins):
                logger.error(
                    f"Model {values['model'].name} has {len(values['model'].pins)} pins {values['model'].pins}. " \
                    + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}.")
                raise AssertionError
            pins = {pin: net for pin, net in zip(values['model'].pins, pins)}
        return pins

    @pydantic.validator('parameters', pre=True)
    def parameters_comply_with_model(cls, parameters, values):
        assert set(parameters).issubset(values['model'].parameters.keys())
        parameters = {k: parameters[k] if k in parameters else v \
            for k, v in values['model'].parameters.items()}
        return parameters

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}='+ (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items())
