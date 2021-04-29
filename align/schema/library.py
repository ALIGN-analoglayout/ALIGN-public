from .model import Model
from .subcircuit import SubCircuit
import inspect
import random
import string
from .types import List, Union, set_context

libraries = {}


class Library(List[Union[Model, SubCircuit]]):

    def __init__(self, name=None, loadbuiltins=True):
        if name:
            assert name not in libraries
            libraries.update({name: self})
        super().__init__()
        if loadbuiltins:
            self.extend(libraries['default'])

    def find(self, name):
        return next((x for x in self if x.name == name.upper()), None)

#
# Create default library
#


default = Library('default')


with set_context(default):
    default.append(
        Model(
            name='NMOS',
            pins=['D', 'G', 'S', 'B'],
            parameters={
                'W': 0,
                'L': 0,
                'NFIN': 1},
            prefix='M'
        )
    )

    default.append(
        Model(
            name='PMOS',
            pins=['D', 'G', 'S', 'B'],
            parameters={
                'W': 0,
                'L': 0,
                'NFIN': 1},
            prefix='M'
        )
    )

    default.append(
        Model(
            name='CAP',
            pins=['+', '-'],
            parameters={
                'VALUE': 0
            },
            prefix='C'
        )
    )

    default.append(
        Model(
            name='RES',
            pins=['+', '-'],
            parameters={
                'VALUE': 0
            },
            prefix='R'
        )
    )
    default.append(
        Model(
            name='IND',
            pins=['+', '-'],
            parameters={
                'VALUE': 0
            },
            prefix='L'
        )
    )
