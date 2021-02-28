import pytest

from align.circuit import elements

# def TEST_SUBCKT(library):
#     assert 'TEST_SUBCKT' not in library
#     subckt = core.SubCircuit('TEST_SUBCKT', 'pin1', 'pin2', library=library, param1=1, param2=1e-3, param3="0.1f", param4="hello")
#     assert 'TEST_SUBCKT' in library
#     assert library['TEST_SUBCKT'] is subckt
#     with pytest.raises(Exception):
#         inst = subckt('X1')
#     with pytest.raises(Exception):
#         inst = subckt('X1', 'net10')
#     inst = subckt('X1', 'net10', 'net12')
#     assert inst.name == 'X1'
#     assert type(inst).__name__ == 'TEST_SUBCKT'
#     assert inst.pins == {'pin1': 'net10', 'pin2': 'net12'}
#     assert list(inst.parameters.keys()) == ['param1', 'param2', 'param3', 'param4']
#     assert inst.parameters['param1'] == 1
#     assert inst.parameters['param2'] - 1e-3 <= 1e-19 # safe floating point comparison
#     assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison
#     assert inst.parameters['param4'] == 'hello'
#     with pytest.raises(Exception):
#         inst = subckt('X1', 'net10', 'net12', garbage='')
#     with pytest.raises(Exception):
#         inst = subckt('X1', 'net10', 'net12', param1='invalid_number')
#     inst = subckt('X1', 'net10', 'net12', param1=2, param3=1e-16)
#     assert inst.parameters['param1'] == 2
#     assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison

def test_NMOS():
    with pytest.raises(Exception):
        inst = elements.NMOS('M1', 'net10', 'net12', 'net13')
    with pytest.raises(Exception):
        inst = elements.NMOS('X1', 'net10', 'net12', 'net13', 'vss')
    inst = elements.NMOS('M1', 'net10', 'net12', 'net13', 'vss')
    assert inst.name == 'M1'
    assert inst.model == 'NMOS'
    assert inst.pins == {'D': 'net10', 'G': 'net12', 'S': 'net13', 'B': 'vss'}
    assert list(inst.parameters.keys()) == ['W', 'L', 'NFIN']
    assert inst.parameters['W'] == 0
    assert inst.parameters['L'] == 0
    assert inst.parameters['NFIN'] == 1
    inst = elements.NMOS('M1', 'net10', 'net12', 'net13', 'vss', NFIN = 2)
    assert inst.parameters['NFIN'] == 2

def test_PMOS():
    with pytest.raises(Exception):
        inst = elements.PMOS('M1', 'net10', 'net12', 'net13')
    with pytest.raises(Exception):
        inst = elements.PMOS('X1', 'net10', 'net12', 'net13', 'vss')
    inst = elements.PMOS('M1', 'net10', 'net12', 'net13', 'vss')
    assert inst.name == 'M1'
    assert inst.model == 'PMOS'
    assert inst.pins == {'D': 'net10', 'G': 'net12', 'S': 'net13', 'B': 'vss'}
    assert list(inst.parameters.keys()) == ['W', 'L', 'NFIN']
    assert inst.parameters['W'] == 0
    assert inst.parameters['L'] == 0
    assert inst.parameters['NFIN'] == 1
    inst = elements.PMOS('M1', 'net10', 'net12', 'net13', 'vss', NFIN = 2)
    assert inst.parameters['NFIN'] == 2

def test_res():
    with pytest.raises(Exception):
        inst = elements.RES('R1', 'net10')
    with pytest.raises(Exception):
        inst = elements.RES('X1', 'net10', 'net12', 1.3)
    inst = elements.RES('R1', 'net10', 'net12', VALUE=1.3)
    assert inst.name == 'R1'
    assert inst.model == 'RES'
    assert inst.pins == {'+': 'net10', '-': 'net12'}
    assert inst.parameters['VALUE'] == 1.3

def test_cap():
    with pytest.raises(Exception):
        inst = elements.CAP('C1', 'net10')
    with pytest.raises(Exception):
        inst = elements.CAP('X1', 'net10', 'net12', 1.3)
    inst = elements.CAP('C1', 'net10', 'net12', VALUE=1.3)
    assert inst.name == 'C1'
    assert inst.model == 'CAP'
    assert inst.pins == {'+': 'net10', '-': 'net12'}
    assert inst.parameters['VALUE'] == 1.3
