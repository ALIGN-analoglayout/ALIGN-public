import pytest

from circuit.core import NTerminalDevice, Circuit, _SubCircuit

def test_n_terminal_device():
    inst = NTerminalDevice('X1')
    assert inst.name == 'X1'
    with pytest.raises(AssertionError):
        inst = NTerminalDevice('X2', 'net1')

def test_2_terminal_device():
    TwoTerminalDevice = type('TwoTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b']})
    with pytest.raises(AssertionError):
        inst = TwoTerminalDevice('X1')
    with pytest.raises(AssertionError):
        inst = TwoTerminalDevice('X1', 'net1')
    with pytest.raises(AssertionError):
        inst = TwoTerminalDevice('X1', 'net1', 'net2')
        inst = TwoTerminalDevice('X1', 'net1', 'net2', nonexistentparameter=2)
    inst = TwoTerminalDevice('X1', 'net1', 'net2')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'TwoTerminalDevice'
    assert inst.pins == {'a': 'net1', 'b': 'net2'}
    assert inst.parameters == {}

def test_subckt_class():
    subckt = type('test_subckt', (_SubCircuit,), {
        '_pins': ['pin1', 'pin2'],
        '_kwargs': {'param1': (int, 1), 'param2': (float, 1e-3), 'param3': (float, 1e-16), 'param4': (str, "hello")}})
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
    assert inst.parameters == {'subckt': 'test_subckt', 'param1': 1, 'param2': 1e-3, 'param3': 1e-16, 'param4': 'hello'}
