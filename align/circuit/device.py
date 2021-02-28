import pydantic
import logging

from typing import Dict, ClassVar, Union, Optional, List
from pydantic import StrictStr, StrictFloat, StrictInt, PrivateAttr
ParamValue = Union[StrictFloat, StrictInt, StrictStr]

logger = logging.getLogger(__name__)
class BaseModel(pydantic.BaseModel):
    '''
    Use this class to define base types such as NMOS, PMOS etc.
    This is likely needed only by align.circuit.elements but
    may be need to be specialized by PDK going forward

    :param name: Name of the model (eg. PMOS)
    :param pins: List of pins (eg. ['D', 'G', 'S', 'B'])
    :param parameters: Dictionary of parameters (eg. {param: 1.0})
    :param prefix: Instance name prefix (eg. M for transistor),
    '''

    name: StrictStr
    pins : List[StrictStr]
    parameters : Dict[StrictStr, ParamValue]
    prefix : Optional[StrictStr]

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False

    @pydantic.validator('pins', always=True)
    def min_pins(cls, pins, values):
        assert len(pins) > 1, 'Device must have at least two terminals'
        return pins

    def __call__(self, name, *pins, **parameters):
        return Device(
            model=self,
            name=name,
            pins=pins,
            parameters=parameters
        )

class Model(pydantic.BaseModel):
    '''
    Use this class to define derived models such as pmos_rvt etc.
    This is almost certain to be needed by the PDK

    :param name: Name of the model (eg. PMOS)
    :param base: instance of class BaseModel
    :param pins: List of pins (eg. ['D', 'G', 'S', 'B'])
    :param parameters: Dictionary of parameters (eg. {param: 1.0})
    :param prefix: Instance name prefix (eg. M for transistor),
    '''

    name: StrictStr
    base: BaseModel = None
    pins : Optional[List[StrictStr]]
    parameters : Optional[Dict[StrictStr, ParamValue]]
    prefix : Optional[StrictStr]

    #
    # Private attributes affecting class behavior
    #

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        validate_all = True

    def __call__(self, name, *pins, **parameters):
        return Device(
            model=self,
            name=name,
            pins=pins,
            parameters=parameters
        )

    @pydantic.validator('base', pre=True, always=True)
    def base_must_be_defined(cls, base, values):
        if not base:
            logger.error( f"Base must be defined for {values['name']}." \
            + 'Did you mean to define BaseModel instead?' )
            raise AssertionError
        return base

    @pydantic.validator('pins', pre=True, always=True)
    def do_not_override_base_pins(cls, pins, values):
        if pins:
            logger.error( f"Inheriting from {values['base'].name}. Cannot add pins" )
            raise AssertionError
        pins = values['base'].pins.copy()
        return pins

    @pydantic.validator('parameters', pre=True, always=True)
    def parameters_must_respect_base_params(cls, parameters, values):
        if not set(parameters).issubset(values['base'].parameters.keys()):
            logger.error(f"Inheriting from {base.name}. Cannot add new parameters")
            raise AssertionError
        parameters = {k: parameters[k] if k in parameters else v \
            for k, v in values['base'].parameters.items()}
        return parameters

    @pydantic.validator('prefix', pre=True, always=True)
    def reuse_base_prefix_if_null(cls, prefix, values):
        if not prefix:
            prefix = values['base'].prefix
        return prefix

Model.update_forward_refs()

class Device(pydantic.BaseModel):

    model: Union[BaseModel, Model]
    name: StrictStr
    pins : Dict[StrictStr, StrictStr]
    parameters : Dict[StrictStr, ParamValue]

    #
    # Private attributes affecting class behavior
    #

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
