import inspect

from . import core
from . import elements

class Library(dict):

    def __init__(self, default=None):
        if default is None:
            default = { x[0]: x[1] for x in
            inspect.getmembers(elements, lambda x: inspect.isclass(x)
                                                    and issubclass(x, core.Device)
                                                    and not x.__name__.startswith('_')) }
        self.update(default)
