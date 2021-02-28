import inspect

from . import device

class Library(dict):

    @property
    def Model(self):
        return self._model

    def __init__(self, name='default', pdk=None):
        self._initialize_library_methods(name)

    def _initialize_library_methods(self, name):
        self._model = type(f'{name}Model', (device.Model, ), {})
        self._model.library = self
