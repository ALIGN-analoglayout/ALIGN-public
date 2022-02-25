import json
from .model import Model
from .subcircuit import SubCircuit
from .types import List, Union, set_context


class Library(List[Union[Model, SubCircuit]]):

    def __init__(self, loadbuiltins=False, pdk_models=None):
        super().__init__()
        models = None
        if pdk_models:
            models = pdk_models()
        elif loadbuiltins:
            models = self.default_models()
        if models:
            with set_context(self):
                for m in models:
                    self.append(m)

    def find(self, name):
        return next((x for x in self if x.name == name.upper()), None)

    def default_models(self):
        models = list()
        models.append(
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
        models.append(
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
        models.append(
            Model(
                name='CAP',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0,
                    'PARALLEL': 1,
                    'STACK': 1
                },
                prefix='C'
            )
        )
        models.append(
            Model(
                name='RES',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0,
                    'PARALLEL': 1,
                    'STACK': 1
                },
                prefix='R'
            )
        )
        models.append(
            Model(
                name='IND',
                pins=['PLUS', 'MINUS'],
                parameters={
                    'VALUE': 0,
                    'PARALLEL': 1,
                    'STACK': 1
                },
                prefix='L'
            )
        )
        return models


def read_lib_json(json_file_path):
    with open(json_file_path, "r") as f:
        data = json.load(f)
    library = Library(loadbuiltins=False)
    with set_context(library):
        for x in data:
            if 'generator' in x:
                library.append(SubCircuit(**{k: v for k, v in x.items() if v}))
            else:
                library.append(Model(**{k: v for k, v in x.items() if v}))
    return library
