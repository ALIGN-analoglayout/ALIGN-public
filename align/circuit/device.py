import pydantic
import logging

from typing import Dict, ClassVar, Union, Optional, List
from typing_extensions import Literal

from . import library
from . import core
from . import constraint

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
    _baseptr = pydantic.PrivateAttr()

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        validate_all = True

    def __init__(self, library = library.default, **data):
        self.__class__.library = library
        super().__init__(**data)
        self.__class__.library.update({self.name: self})
        if self.base:
            self._baseptr = library[self.base]

    def __call__(self, name, *pins, **parameters):
        return Instance(
            model=self.name,
            library=self.library,
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

class SubCircuit(Model):

    _circuit = pydantic.PrivateAttr()
    constraint = constraint.ConstraintDB()

    @property
    def circuit(self):
        return self._circuit

    def __init__(self, *args, **kwargs):
        self._circuit = core.Circuit()
        kwargs['constraint'] = constraint.ConstraintDB()
        Model.__init__(self, *args, **kwargs)

    def __getattr__(self, name):
        return getattr(self._circuit, name)

    class Config(Model.Config):
        arbitrary_types_allowed = True

    def xyce(self):
        ret = []
        for constraint in self.constraint.constraints:
            ret.append(f'* @: {constraint}')
        ret.append(f'.SUBCKT {self.name} ' + ' '.join(f'{x}' for x in self.pins))
        ret.extend([f'.PARAM {x}=' + (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items()])
        ret.append(self.circuit.xyce())
        ret.append(f'.ENDS {self.name}')
        return '\n'.join(ret)

class Instance(pydantic.BaseModel):

    type: Literal['Instance'] = 'Instance'
    model: Union[Model, SubCircuit]
    name: str
    pins : Dict[str, str]
    parameters : Dict[str, str]

    #
    # Private attributes affecting class behavior
    #

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False

    jsonfilter: ClassVar[Dict] = {
        'type': ...,
        'model': {'name'},
        'name': ...,
        'pins' : ...,
        'parameters' : ...
    }

    library : ClassVar[Dict] = None

    def __init__(self, library=None, **data):
        # This is only to help with JSON deserialization
        if isinstance(data['model'], str):
            assert library is not None
            data['model'] = library[data['model']]
        super().__init__(**data)

    @property
    def m(self):
        return self.model

    @pydantic.validator('name')
    def name_complies_with_model(cls, name, values):
        name = name.upper()
        if values['model'].prefix:
            if not name.startswith(values['model'].prefix):
                logger.error(f"{name} does not start with {values['model'].prefix}")
                raise AssertionError(f"{name} does not start with {values['model'].prefix}")
        return name

    @pydantic.validator('pins', pre=True)
    def pins_comply_with_model(cls, pins, values):
        if isinstance(pins, dict):
            pins = {k.upper(): v.upper() for k, v in pins.items()}
            assert set(pins.keys()) == set(values['model'].pins)
        else:
            # TODO: This is not integral to Instance class
            #       Move to Model.__call__ instead
            if len(pins) != len(values['model'].pins):
                logger.error(
                    f"Model {values['model'].name} has {len(values['model'].pins)} pins {values['model'].pins}. " \
                    + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}.")
                raise AssertionError(
                    f"Model {values['model'].name} has {len(values['model'].pins)} pins {values['model'].pins}. " \
                    + f"{len(pins)} nets {pins} were passed when instantiating {values['name']}.")
            pins = {pin: net.upper() for pin, net in zip(values['model'].pins, pins)}
        return pins

    @pydantic.validator('parameters')
    def parameters_comply_with_model(cls, parameters, values):
        if parameters:
            parameters = {k.upper(): v.upper() for k, v in parameters.items()}
        else:
            parameters = {}
        assert set(parameters.keys()).issubset(values['model'].parameters.keys())
        parameters = {k: parameters[k] if k in parameters else v \
            for k, v in values['model'].parameters.items()}
        return parameters

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}={{{y}}}' for x, y in self.parameters.items())


from . import core
from . import constraint