from .types import Optional, List, Dict

from . import types

from .model import Model
from .instance import Instance
from .constraint import ConstraintDB


class SubCircuit(Model):

    name : str                 # Model Name
    pins : Optional[List[str]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    elements: List[Instance]
    constraints: ConstraintDB
    prefix : str = 'X'         # Instance name prefix, optional

    @types.validate_arguments
    def add(self, instance: Instance):
        self.elements.append(instance)
        return instance

    @property
    def nets(self):
        nets = []
        for element in self.elements:
            nets.extend(x for x in element.pins.values() if x not in nets)
        return nets

    def __init__(self, *args, **kwargs):
        if 'elements' not in kwargs:
            kwargs['elements'] = []
        if 'constraints' not in kwargs:
            kwargs['constraints'] = ConstraintDB()
        super().__init__(*args, **kwargs)

    def xyce(self):
        ret = []
        for constraint in self.constraints:
            ret.append(f'* @: {constraint}')
        ret.append(f'.SUBCKT {self.name} ' + ' '.join(f'{x}' for x in self.pins))
        ret.extend([f'.PARAM {x}=' + (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items()])
        ret.extend([element.xyce() for element in self.elements])
        ret.append(f'.ENDS {self.name}')
        return '\n'.join(ret)


class Circuit(SubCircuit):

    name: Optional[str]
    pins: Optional[List[str]]

    def xyce(self):
        return '\n'.join([element.xyce() for element in self.elements])

    @types.validator('pins')
    def pin_check(cls, pins, values):
        if pins:
            pins = [p.upper() for p in pins]
        return pins
