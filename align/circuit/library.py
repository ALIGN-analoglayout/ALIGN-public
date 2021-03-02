import inspect
import random
import string

libraries = {}

class Library(dict):

    def __init__(self, name=None, loadbuiltins=True):
        if name:
            assert name not in libraries
            libraries.update({name: self})
        if loadbuiltins:
            self.update(libraries['default'])

default = Library('default')
