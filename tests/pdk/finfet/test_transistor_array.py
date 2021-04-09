from align.pdk.finfet import MOSGenerator
from .helper import *


def test_array_one():
    c = MOSGenerator()
    ports = {'SA': [('M1', 'S')], 'DA': [('M1', 'D')], 'GA': [('M1', 'G')]}
    parameters = {'m': 4, 'nf': 2, 'real_inst_type': 'n'}
    c.addNMOSArray(None, 2, 1, None, ports, **parameters)
    fn = "test_transistor_array_1"
    compare_with_golden(fn, c)


def test_array_two():
    c = MOSGenerator()
    ports = {'S': [('M1', 'S'), ('M2', 'S')],
             'DA': [('M1', 'D')], 'DB': [('M2', 'D')],
             'GA': [('M1', 'G')], 'GB': [('M2', 'G')]
             }
    parameters = {'m': 4, 'stack': 4, 'real_inst_type': 'n'}
    c.addNMOSArray(None, 1, 1, None, ports, **parameters)
    fn = "test_transistor_array_2"
    compare_with_golden(fn, c)
