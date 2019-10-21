import pytest

import circuit.elements as elements

def test_subckt():
    assert 'test_subckt' not in elements.library
    subckt = elements.SubCircuit('test_subckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3="0.1f", param4="hello")
    assert 'test_subckt' in elements.library
    assert elements.library['test_subckt'] is subckt
    with pytest.raises(AssertionError):
        inst = subckt('X1')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10')
    inst = subckt('X1', 'net10', 'net12')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'test_subckt'
    assert inst.pins == {'pin1': 'net10', 'pin2': 'net12'}
    assert list(inst.parameters.keys()) == ['param1', 'param2', 'param3', 'param4']
    assert inst.parameters['param1'] == 1
    assert inst.parameters['param2'] - 1e-3 <= 1e-19 # safe floating point comparison
    assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison
    assert inst.parameters['param4'] == 'hello'
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10', 'net12', garbage='')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10', 'net12', param1='invalid_number')
    inst = subckt('X1', 'net10', 'net12', param1=2, param3=1e-16)
    assert inst.parameters['param1'] == 2
    assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison

def test_library():
    lib = elements.Library()
    assert 'test_subckt' not in lib
    subckt = elements.SubCircuit('test_subckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3="0.1f", param4="hello", library=lib)
    assert 'test_subckt' in lib
    assert lib['test_subckt'] is subckt

def test_NMOS():
    assert 'NMOS' in elements.library
    assert elements.library['NMOS'] is elements.NMOS
    with pytest.raises(AssertionError):
        inst = elements.NMOS('M1', 'net10', 'net12', 'net13')
    with pytest.raises(AssertionError):
        inst = elements.NMOS('X1', 'net10', 'net12', 'net13', 'vss')
    inst = elements.NMOS('M1', 'net10', 'net12', 'net13', 'vss')
    assert inst.name == 'M1'
    assert type(inst).__name__ == 'NMOS'
    assert inst.pins == {'D': 'net10', 'G': 'net12', 'S': 'net13', 'B': 'vss'}
    assert list(inst.parameters.keys()) == ['w', 'l', 'nfin']
    assert inst.parameters['w'] == 0
    assert inst.parameters['l'] == 0
    assert inst.parameters['nfin'] == 1
    inst = elements.NMOS('M1', 'net10', 'net12', 'net13', 'vss', nfin = 2)
    assert inst.parameters['nfin'] == 2
    with pytest.raises(AssertionError):
        inst = elements.NMOS('M1', 'net10', 'net12', 'net13', 'vss', nfin = 1.5)

def test_PMOS():
    assert 'PMOS' in elements.library
    assert elements.library['PMOS'] is elements.PMOS
    with pytest.raises(AssertionError):
        inst = elements.PMOS('M1', 'net10', 'net12', 'net13')
    with pytest.raises(AssertionError):
        inst = elements.PMOS('X1', 'net10', 'net12', 'net13', 'vss')
    inst = elements.PMOS('M1', 'net10', 'net12', 'net13', 'vss')
    assert inst.name == 'M1'
    assert type(inst).__name__ == 'PMOS'
    assert inst.pins == {'D': 'net10', 'G': 'net12', 'S': 'net13', 'B': 'vss'}
    assert list(inst.parameters.keys()) == ['w', 'l', 'nfin']
    assert inst.parameters['w'] == 0
    assert inst.parameters['l'] == 0
    assert inst.parameters['nfin'] == 1
    inst = elements.PMOS('M1', 'net10', 'net12', 'net13', 'vss', nfin = 2)
    assert inst.parameters['nfin'] == 2
    with pytest.raises(AssertionError):
        inst = elements.PMOS('M1', 'net10', 'net12', 'net13', 'vss', nfin = 1.5)

def test_res():
    assert elements.RES.__name__ in elements.library
    assert elements.library[elements.RES.__name__] is elements.RES
    assert elements.RES in elements.library.values()
    with pytest.raises(AssertionError):
        inst = elements.RES('R1', 'net10')
    with pytest.raises(AssertionError):
        inst = elements.RES('X1', 'net10', 'net12', 1.3)
    inst = elements.RES('R1', 'net10', 'net12', value=1.3)
    assert inst.name == 'R1'
    assert type(inst).__name__ == 'RES'
    assert inst.pins == {'plus': 'net10', 'minus': 'net12'}
    assert inst.parameters['value'] == 1.3

def test_cap():
    assert elements.CAP.__name__ in elements.library
    assert elements.CAP in elements.library.values()
    with pytest.raises(AssertionError):
        inst = elements.CAP('C1', 'net10')
    with pytest.raises(AssertionError):
        inst = elements.CAP('X1', 'net10', 'net12', 1.3)
    inst = elements.CAP('C1', 'net10', 'net12', value=1.3)
    assert inst.name == 'C1'
    assert type(inst).__name__ == 'CAP'
    assert inst.pins == {'plus': 'net10', 'minus': 'net12'}
    assert inst.parameters['value'] == 1.3
