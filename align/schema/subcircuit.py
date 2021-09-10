from .types import Optional, List, Dict, String

from . import types
from pydantic import validator

from .types import set_context
from .model import Model
from .instance import Instance
from .constraint import ConstraintDB

class SubCircuit(Model):
    name : String                 # Model Name
    pins : Optional[List[String]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[String, String]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    elements: List[Instance]
    constraints: ConstraintDB
    prefix : String = 'X'         # Instance name prefix, optional

    @property
    def nets(self):
        nets = []
        for element in self.elements:
            nets.extend(x for x in element.pins.values() if x not in nets)
        return nets

    def get_element(self, name):
        return next((x for x in self.elements if x.name == name), None)

    def update_element(self,name,kwargs):
        i, inst = next(((i,x) for i,x in enumerate(self.elements) if x.name == name),None)
        with set_context(self.elements):
            new_inst = Instance(name=name,
                model= (kwargs['model'] if 'model' in kwargs else inst.model),
                pins= (kwargs['pins'] if 'pins' in kwargs else inst.pins),
                parameters= (kwargs['parameters'] if 'parameters' in kwargs else inst.parameters),
                generator= (kwargs['generator'] if 'generator' in kwargs else inst.generator)
                )
            self.elements[i] = new_inst

    def __init__(self, *args, **kwargs):
        # make elements optional in __init__
        # TODO: Replace with default factory
        if 'elements' not in kwargs:
            kwargs['elements'] = []
        # defer constraint processing for now
        constraints = []
        if 'constraints' in kwargs:
            constraints = kwargs['constraints']
        kwargs['constraints'] = []
        # load subcircuit
        super().__init__(*args, **kwargs)
        # process constraints
        with types.set_context(self.constraints):
            self.constraints.extend(constraints)
    #TODO: Add validator for duplicate name
    #TODO: Add validator for duplicate pins

    def xyce(self):
        ret = []
        for constraint in self.constraints:
            ret.append(f'* @: {constraint}')
        ret.append(f'.SUBCKT {self.name} ' + ' '.join(f'{x}' for x in self.pins))
        ret.extend([f'.PARAM {x}=' + (f'{{{y}}}' if isinstance(y, String) else f'{y}') for x, y in self.parameters.items()])
        ret.extend([element.xyce() for element in self.elements])
        ret.append(f'.ENDS {self.name}')
        return '\n'.join(ret)


class Circuit(SubCircuit):

    name: Optional[String]
    pins: Optional[List[String]]

    def xyce(self):
        return '\n'.join([element.xyce() for element in self.elements])

    @types.validator('pins')
    def pin_check(cls, pins, values):
        return pins

    @types.validator('name', allow_reuse=True)
    def name_is_unique(cls, name, values):
        assert isinstance(cls._validator_ctx().parent, List[Instance]), 'subckt can only be instanitated within List[Instance]'
        assert cls._validator_ctx().parent is not None, 'subckt can only be instantiated within a library'
        assert cls._validator_ctx().parent.find(name) is None, f'Existing subckt definition found {name}'
        return name
