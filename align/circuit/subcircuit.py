import pydantic
from typing import Optional, List

from . import model
from . import instance
from . import constraint
from . import netlist

class SubCircuit(model.Model):

    constraint : constraint.ConstraintDB

    @property
    def netlist(self):
        return self._netlist

    def add(self, instance):
        return self._netlist.add(instance)

    def remove(self, instance):
        self._netlist.remove(instance)

    @property
    def elements(self):
        return self._netlist.elements

    @property
    def nets(self):
        return self._netlist.nets

    def __init__(self, *args, **kwargs):
        self._netlist = netlist.Netlist(self)
        if 'constraint' not in kwargs:
            kwargs['constraint'] = constraint.ConstraintDB()
        super().__init__(*args, **kwargs)

    _netlist = pydantic.PrivateAttr()

    class Config(model.Model.Config):
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

    def flatten(self, depth=999):
        self.netlist.flatten(depth)

    def replace_matching_subckts(self, subckts, node_match=None, edge_match=None):
        self.netlist.replace_matching_subckts(subckts, node_match, edge_match)

class Circuit(SubCircuit):

    name: Optional[str]
    pins: Optional[List[str]]

    def xyce(self):
        return self.netlist.xyce()

    @pydantic.validator('pins')
    def pin_check(cls, pins, values):
        if pins:
            pins = [p.upper() for p in pins]
        return pins
