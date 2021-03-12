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

#
# Create default library
#

default = Library('default')

from .model import Model

default['NMOS'] = Model(
    name='NMOS',
    pins=['D', 'G', 'S', 'B'],
    parameters={
        'W': 0,
        'L': 0,
        'NFIN': 1},
    prefix = 'M')

default['PMOS'] = Model(
    name='PMOS',
    pins=['D', 'G', 'S', 'B'],
    parameters={
        'W': 0,
        'L': 0,
        'NFIN': 1},
    prefix = 'M')

default['CAP'] = Model(
    name='CAP',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'C'
    )

default['RES'] = Model(
    name='RES',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'R'
    )

default['IND'] = Model(
    name='IND',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'L'
    )
