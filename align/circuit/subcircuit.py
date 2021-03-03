import pydantic

from . import model
from . import constraint
from . import netlist

class SubCircuit(model.Model):

    _circuit = pydantic.PrivateAttr()
    constraint : constraint.ConstraintDB

    @property
    def circuit(self):
        return self._circuit

    def __init__(self, *args, **kwargs):
        self._circuit = netlist.Netlist()
        kwargs['constraint'] = constraint.ConstraintDB()
        model.Model.__init__(self, *args, **kwargs)

    def __getattr__(self, name):
        return getattr(self._circuit, name)

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

