import sys, inspect

from .core import NTerminalDevice, Device

# WARNING: All pin & parameter names must be capitalized
#          to support case-insensitive parsing

NMOS = NTerminalDevice(
    'NMOS',
    'D', 'G', 'S', 'B',
    W = 0, L = 0, NFIN = 1,
    prefix = 'M')

PMOS = NTerminalDevice(
    'PMOS',
    'D', 'G', 'S', 'B',
    W = 0, L = 0, NFIN = 1,
    prefix = 'M')

CAP = NTerminalDevice(
    'CAP',
    '+', '-',
    VALUE = 0,
    prefix = 'C'
    )

RES = NTerminalDevice(
    'RES',
    '+', '-',
    VALUE = 0,
    prefix = 'R'
    )

IND = NTerminalDevice(
    'IND',
    '+', '-',
    VALUE = 0,
    prefix = 'L'
    )

class Library(dict):

    def __init__(self, default=None):
        if default is None:
            default = { x[0]: x[1] for x in
            inspect.getmembers(sys.modules[__name__], lambda x: inspect.isclass(x) and
                                                                issubclass(x, Device) and
                                                                not x.__name__.startswith('_')) }
        self.update(default)
