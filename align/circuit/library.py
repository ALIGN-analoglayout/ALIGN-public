import inspect
import random
import string

from . import device

libraries = {}

class Library(dict):

    def __init__(self, name=None, pdk=None):
        if name:
            assert name not in libraries
        else:
            name = self._gen_lib_name()
        libraries.update({name: self})

    def _gen_lib_name(self, nchar=8):
        name = 'LIB' + ''.join(random.choices(string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_lib_name(nchar) if name in libraries else name

default = Library('default')
