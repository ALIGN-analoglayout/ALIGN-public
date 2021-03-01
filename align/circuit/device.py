import pydantic
import logging

from typing import Dict, ClassVar, Union, Optional, List
from typing_extensions import Literal

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

    type : Literal['Model'] = 'Model'
    name : str
    base : Optional[str]       # Optional for Base Models
    pins : Optional[List[str]] # Optional when inheriting
    parameters : Optional[Dict[str, str]]
    prefix : Optional[str]     # Always optional

    #
    # Private attributes affecting class behavior
    #

    library : ClassVar[library.Library]

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        validate_all = True

    def __init__(self, library = library.default, **data):
        self.__class__.library = library
        super().__init__(**data)
        self.__class__.library.update(
            {self.name: self}
        )

    def __call__(self, name, *pins, **parameters):
        return Device(
            model=self.name,
            library=self.library,
            name=name,
            pins=pins,
            parameters=parameters
        )

    @pydantic.validator('name')
    def name_check(cls, name):
        assert len(name) > 0
        return name.upper()

    @pydantic.validator('base', pre=True, always=True)
    def base_check(cls, base, values):
        if base:
            base = base.upper()
            if base not in cls.library:
                logger.error(f'Could not find {base} in library')
                raise AssertionError(f'Could not find {base} in library')
        return base

    @pydantic.validator('pins', always=True)
    def pin_check(cls, pins, values):
        if 'base' not in values or not values['base']:
            assert len(pins) > 1, 'Device must have at least two terminals'
            pins = [p.upper() for p in pins]
        elif pins:
            logger.error(f"Inheriting from {values['base'].name}. Cannot add pins")
            raise AssertionError(f"Inheriting from {values['base'].name}. Cannot add pins")
        else:
            pins = cls.library[values['base']].pins.copy()
        return pins

    @pydantic.validator('parameters', always=True)
    def parameter_check(cls, parameters, values):
        if parameters:
            parameters = {k.upper(): v.upper() for k, v in parameters.items()}
        else:
            parameters = {}
        if 'base' not in values or not values['base']:
            assert cls.__name__ != 'Model' or len(parameters) > 0, 'BaseModel should have one or more parameters'
        elif not set(parameters.keys()).issubset(cls.library[values['base']].parameters.keys()):
            logger.error(f"Inheriting from {values['base']}. Cannot add new parameters")
            raise AssertionError(f"Inheriting from {values['base']}. Cannot add new parameters")
        else:
            parameters = {k.upper(): parameters[k].upper() if k in parameters else v \
                for k, v in cls.library[values['base']].parameters.items()}
        return parameters

    @pydantic.validator('prefix', always=True)
    def prefix_check(cls, prefix, values):
        if 'base' in values and values['base']:
            prefix = cls.library[values['base']].prefix
        return prefix

class Device(pydantic.BaseModel):

    type: Literal['Device'] = 'Device'
    model: str
    name: str
    pins : Dict[str, str]
    parameters : Dict[str, str]

    #
    # Private attributes affecting class behavior
    #

    library : ClassVar[Dict] = None
    _moduleptr = pydantic.PrivateAttr()

    def __init__(self, library=None, **data):
        assert library is not None
        self.__class__.library = library
        super().__init__(**data)
        self._moduleptr = library[self.model]

    @property
    def m(self):
        return self._moduleptr

    @pydantic.validator('model', pre=True, always=True)
    def model_check(cls, model):
        if cls.library is None:
            assert model in cls.library
        return model

    @pydantic.validator('name')
    def name_complies_with_model(cls, name, values):
        name = name.upper()
        if cls.library[values['model']].prefix:
            if not name.startswith(cls.library[values['model']].prefix):
                logger.error(f"{name} does not start with {cls.library[values['model']].prefix}")
                raise AssertionError(f"{name} does not start with {cls.library[values['model']].prefix}")
        return name

    @pydantic.validator('pins', pre=True)
    def pins_comply_with_model(cls, pins, values):
        if isinstance(pins, dict):
            pins = {k.upper(): v.upper() for k, v in pins.items()}
            assert set(pins.keys()) == set(cls.library[values['model']].pins)
        else:
            if len(pins) != len(cls.library[values['model']].pins):
                logger.error(
                    f"Model {cls.library[values['model']].name} has {len(cls.library[values['model']].pins)} pins {cls.library[values['model']].pins}. " \
                    + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}.")
                raise AssertionError(
                    f"Model {cls.library[values['model']].name} has {len(cls.library[values['model']].pins)} pins {cls.library[values['model']].pins}. " \
                    + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}.")
            pins = {pin: net.upper() for pin, net in zip(cls.library[values['model']].pins, pins)}
        return pins

    @pydantic.validator('parameters')
    def parameters_comply_with_model(cls, parameters, values):
        if parameters:
            parameters = {k.upper(): v.upper() for k, v in parameters.items()}
        else:
            parameters = {}
        assert set(parameters.keys()).issubset(cls.library[values['model']].parameters.keys())
        parameters = {k: parameters[k] if k in parameters else v \
            for k, v in cls.library[values['model']].parameters.items()}
        return parameters

    def __getattr__(self, name):
        if name in self.__dict__:
            return self.__dict__['name']
        elif hasattr(self.m, name):
            return getattr(self.m, name)
        else:
            raise AttributeError

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}='+ (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items())
