from . import types
from .types import Union, Dict, Optional, List, String, set_context

import logging
logger = logging.getLogger(__name__)

class Instance(types.BaseModel):

    model: String
    name: String
    pins : Dict[String, String]
    parameters : Optional[Dict[String, String]]
    #TODO: associate a generator for eacj primitive during instantiation
    generator: String #Handles different sized instantiation of same subcircuit to same generator
    abstract_name: Optional[String] # Added during primitive generator, in case no primitive generator found = generator
    class Config:
        allow_mutation = True

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}={{{y}}}' for x, y in self.parameters.items())

    #
    # Private attributes affecting class behavior
    #

    @staticmethod
    def _get_model(library, name):
        return next((x for x in library if x.name == name), None)

    def add_generator(self,gen):
        with set_context(self.parent):
            self.generator = gen
    def add_abs_name(self,abn):
        with set_context(self.parent):
            self.abstract_name = abn
    def add_actual_name(self, acn):
        with set_context(self.parent):
            self.actual_name = acn

    @property
    def mclass(self):
        model = self._get_model(self.parent.parent.parent, self.model)
        assert model is not None, self.parent.parent.parent
        return model

    @types.validator('model', allow_reuse=True)
    def model_exists_in_library(cls, model):
        assert isinstance(cls._validator_ctx().parent, List[Instance]), 'Instance can only be instanitated within List[Instance]'
        assert cls._validator_ctx().parent.parent is not None, 'List[Instance] can only be instantiated within a SubCircuit / Circuit'
        assert cls._validator_ctx().parent.parent.parent is not None, 'Circuit / SubCircuit constaining instance must be registered to a Library'
        assert cls._get_model(cls._validator_ctx().parent.parent.parent, model) is not None, f'Could not find model {model}'
        return model

    @types.validator('name', allow_reuse=True)
    def name_complies_with_model(cls, name, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        if model.prefix and not name.startswith(model.prefix):
            logger.error(f"{name} does not start with {model.prefix}")
            raise AssertionError(f"{name} does not start with {model.prefix}")
        return name

    @types.validator('pins', allow_reuse=True)
    def pins_comply_with_model(cls, pins, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        assert set(pins.keys()) == set(model.pins), f'{set(pins.keys())} do not match {set(model.pins)}'
        return pins

    @types.validator('parameters', allow_reuse=True, always=True)
    def parameters_comply_with_model(cls, parameters, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        if parameters:
            assert model.parameters and set(parameters.keys()).issubset(model.parameters.keys()), \
                f"{cls.__name__} parameters must be a subset of {model.__class__.__name__} parameters"
            parameters = type(parameters)({**model.parameters, **parameters})
        elif model.parameters:
            parameters = model.parameters.copy()
        return parameters
