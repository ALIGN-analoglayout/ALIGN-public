import pytest

from circuit.circuit import *

def test_n_terminal_device():
    inst = NTerminalDevice('X1')
    assert inst.name == 'X1'
    with pytest.raises(AssertionError):
        inst = NTerminalDevice('X2', 'net1')

def test_subckt():
    subckt = SubCircuit('test_subckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3="0.1f", param4="hello")
    assert subckt in library
    with pytest.raises(AssertionError):
        inst = subckt('X1')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10', 'net12')
    inst = subckt('X1', 'net10', 'net12', 'test_subckt')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'test_subckt'
    assert inst.pins == {'pin1': 'net10', 'pin2': 'net12'}
    assert list(inst.parameters.keys()) == ['subckt', 'param1', 'param2', 'param3', 'param4']
    assert inst.parameters['subckt'] == 'test_subckt'
    assert inst.parameters['param1'] == 1
    assert inst.parameters['param2'] - 1e-3 <= 1e-19 # safe floating point comparison
    assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison
    assert inst.parameters['param4'] == 'hello'
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10', 'net12', 'test_subckt', garbage='')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10', 'net12', 'test_subckt', param1='invalid_number')
    inst = subckt('X1', 'net10', 'net12', 'test_subckt', param1=2, param3=1e-16)
    assert inst.parameters['param1'] == 2
    assert inst.parameters['param3'] - 1e-16 <= 1e-19 # safe floating point comparison

def test_mosfet():
    with pytest.raises(AssertionError):
        inst = MosFET('M1', 'net10', 'net12', 'net13')
    with pytest.raises(AssertionError):
        inst = MosFET('M1', 'net10', 'net12', 'net13', 'vss')
    with pytest.raises(AssertionError):
        inst = MosFET('X1', 'net10', 'net12', 'net13', 'vss', 'nfet')
    inst = MosFET('M1', 'net10', 'net12', 'net13', 'vss', 'nfet')
    assert inst.name == 'M1'
    assert type(inst).__name__ == 'MosFET'
    assert inst.pins == {'D': 'net10', 'G': 'net12', 'S': 'net13', 'B': 'vss'}
    assert list(inst.parameters.keys()) == ['model', 'w', 'l', 'nfin']
    assert inst.parameters['model'] == 'nfet'
    assert inst.parameters['w'] == 0
    assert inst.parameters['l'] == 0
    assert inst.parameters['nfin'] == 1
    inst = MosFET('M1', 'net10', 'net12', 'net13', 'vss', 'nfet', nfin = 2)
    assert inst.parameters['nfin'] == 2
    with pytest.raises(AssertionError):
        inst = MosFET('M1', 'net10', 'net12', 'net13', 'vss', 'nfet', nfin = 1.5)

def test_res():
    with pytest.raises(AssertionError):
        inst = Resistor('R1', 'net10')
    with pytest.raises(AssertionError):
        inst = Resistor('R1', 'net10', 'net12')
    with pytest.raises(AssertionError):
        inst = Resistor('X1', 'net10', 'net12', 1.3)
    inst = Resistor('R1', 'net10', 'net12', 1.3)
    assert inst.name == 'R1'
    assert type(inst).__name__ == 'Resistor'
    assert inst.pins == {'plus': 'net10', 'minus': 'net12'}
    assert inst.parameters['value'] == 1.3

def test_cap():
    with pytest.raises(AssertionError):
        inst = Capacitor('C1', 'net10')
    with pytest.raises(AssertionError):
        inst = Capacitor('C1', 'net10', 'net12')
    with pytest.raises(AssertionError):
        inst = Capacitor('X1', 'net10', 'net12', 1.3)
    inst = Capacitor('C1', 'net10', 'net12', 1.3)
    assert inst.name == 'C1'
    assert type(inst).__name__ == 'Capacitor'
    assert inst.pins == {'plus': 'net10', 'minus': 'net12'}
    assert inst.parameters['value'] == 1.3
