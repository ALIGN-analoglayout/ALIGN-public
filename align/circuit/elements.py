import sys, inspect

from .core import NTerminalDevice

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

