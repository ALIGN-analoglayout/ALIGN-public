import sys, inspect

from .model import Model

# WARNING: All pin & parameter names must be capitalized
#          to support case-insensitive parsing

NMOS = Model(
    name='NMOS',
    pins=['D', 'G', 'S', 'B'],
    parameters={
        'W': 0,
        'L': 0,
        'NFIN': 1},
    prefix = 'M')

PMOS = Model(
    name='PMOS',
    pins=['D', 'G', 'S', 'B'],
    parameters={
        'W': 0,
        'L': 0,
        'NFIN': 1},
    prefix = 'M')

CAP = Model(
    name='CAP',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'C'
    )

RES = Model(
    name='RES',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'R'
    )

IND = Model(
    name='IND',
    pins=['+', '-'],
    parameters={
        'VALUE': 0
    },
    prefix = 'L'
    )

