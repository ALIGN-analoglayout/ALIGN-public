import inspect

from . import device

libraries = {}

class Library(dict):

    def __init__(self, name='default', pdk=None):
        if name in libraries:
            self.update(libraries[name])
        libraries.update({name: self})

default = Library('default')
