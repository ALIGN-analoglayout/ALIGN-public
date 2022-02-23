from . import types
from .types import Union, Dict, Optional, List, set_context

import logging
logger = logging.getLogger(__name__)

class Instance(types.BaseModel):

    model: str
    name: str
    pins : Dict[str, str]
    parameters : Optional[Dict[str, str]]
    abstract_name: Optional[str] # unique name based on model and parameters
    class Config:
        allow_mutation = True

    def xyce(self):
        return f'{self.name} ' + \
            ' '.join(self.pins.values()) + \
            f' {self.model.name} ' + \
            ' '.join(f'{x}={{{y}}}' for x, y in self.parameters.items())

    def translate(self, solver):
        '''
        Bounding boxes must have non-zero
        height & width
        '''
        b = solver.bbox_vars(self.name)
        yield b.llx < b.urx
        yield b.lly < b.ury

    #
    # Private attributes affecting class behavior
    #

    @staticmethod
    def _get_model(library, name):
        return next((x for x in library if x.name == name), None)

    def add_abs_name(self,abn):
        with set_context(self.parent):
            self.abstract_name = abn

    @property
    def mclass(self):
        model = self._get_model(self.parent.parent.parent, self.model)
        assert model is not None, self.parent.parent.parent
        return model

    @types.validator('model', allow_reuse=True)
    def model_exists_in_library(cls, model):
        model = model.upper()
        assert isinstance(cls._validator_ctx().parent, List[Instance]), 'Instance can only be instanitated within List[Instance]'
        assert cls._validator_ctx().parent.parent is not None, 'List[Instance] can only be instantiated within a SubCircuit / Circuit'
        assert cls._validator_ctx().parent.parent.parent is not None, 'Circuit / SubCircuit constaining instance must be registered to a Library'
        assert cls._get_model(cls._validator_ctx().parent.parent.parent, model) is not None, f'Could not find model {model}'
        return model

    @types.validator('name', allow_reuse=True)
    def name_complies_with_model(cls, name, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        name = name.upper()
        if model.prefix and not name.startswith(model.prefix):
            logger.error(f"{name} does not start with {model.prefix}")
            raise AssertionError(f"{name} does not start with {model.prefix}")
        return name

    @types.validator('pins', allow_reuse=True)
    def pins_comply_with_model(cls, pins, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        pins = {k.upper(): v.upper() for k, v in pins.items()}
        assert set(pins.keys()) == set(model.pins)
        return pins

    @types.validator('parameters', allow_reuse=True, always=True)
    def parameters_comply_with_model(cls, parameters, values):
        assert 'model' in values, 'Cannot run check without model definition'
        model = cls._get_model(cls._validator_ctx().parent.parent.parent, values['model'])
        if parameters:
            parameters = {k.upper(): v.upper() for k, v in parameters.items()}
            assert model.parameters and set(parameters.keys()).issubset(model.parameters.keys()), \
                f"{cls.__name__} parameters must be a subset of {model.__class__.__name__} parameters"
            parameters = {k: parameters[k] if k in parameters else v \
                for k, v in model.parameters.items()}
        elif model.parameters:
            parameters = model.parameters.copy()
        return parameters
