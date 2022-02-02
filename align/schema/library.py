from .model import Model
from .subcircuit import SubCircuit
from .types import List, Union, set_context

libraries = {}


class Library(List[Union[Model, SubCircuit]]):

    def __init__(self, name=None, loadbuiltins=False, pdk_models=None):
        if name:
            assert name not in libraries
            libraries.update({name: self})
        super().__init__()
        if loadbuiltins:
            load_builtins(default)
            self.extend(libraries['default'])
        if pdk_models:
            with set_context(default):
                for m in pdk_models:
                    default.append(m)
            self.extend(libraries['default'])

    def find(self, name):
        return next((x for x in self if x.name == name.upper()), None)


#
# Create default library
#
default = Library('default')


def load_builtins(default):
    with set_context(default):
        default.append(
            Model(
                name='NMOS',
                pins=['D', 'G', 'S', 'B'],
                parameters={
                    'W': 0,
                    'L': 0,
                    'NFIN': 1,
                    'NF': 2,
                    'M': 1,
                    'PARALLEL': 1,  # Internal attribute used for parallel and stacked devices
                    'STACK': 1},
                prefix=''
            )
        )
        default.append(
            Model(
                name='PMOS',
                pins=['D', 'G', 'S', 'B'],
                parameters={
                    'W': 0,
                    'L': 0,
                    'NFIN': 1,
                    'NF': 2,
                    'M': 1,
                    'PARALLEL': 1,  # Internal attribute used for parallel and stacked devices
                    'STACK': 1},
                prefix=''
            )
        )
        default.append(
            Model(
                name='CAP',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0
                },
                prefix='C'
            )
        )
        default.append(
            Model(
                name='RES',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0
                },
                prefix='R'
            )
        )
        default.append(
            Model(
                name='IND',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0
                },
                prefix='L'
            )
        )
