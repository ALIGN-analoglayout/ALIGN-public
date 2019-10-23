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

def test_3_terminal_device_w_parameter():
    MyThreeTerminalDevice = type('MyThreeTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b', 'c'], '_parameters': {'myparameter': (int, 1)}})
    with pytest.raises(AssertionError):
        inst = MyThreeTerminalDevice('X1')
    with pytest.raises(AssertionError):
        inst = MyThreeTerminalDevice('X1', 'net1')
    with pytest.raises(AssertionError):
        inst = MyThreeTerminalDevice('X1', 'net1', 'net2')
    with pytest.raises(AssertionError):
        inst = MyThreeTerminalDevice('X1', 'net1', 'net2', 'net3', garbageparameter=2)
    inst = MyThreeTerminalDevice('X1', 'net1', 'net2', 'net3')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'MyThreeTerminalDevice'
    assert inst.pins == {'a': 'net1', 'b': 'net2', 'c': 'net3'}
    assert inst.parameters == {'myparameter': 1}
    inst = MyThreeTerminalDevice('X1', 'net1', 'net2', 'net3', myparameter = 2)
    assert inst.parameters == {'myparameter': 2}

def test_subckt_class():
    subckt = type('test_subckt', (_SubCircuit,), {
        '_pins': ['pin1', 'pin2'],
        '_parameters': {'param1': (int, 1), 'param2': (float, 1e-3), 'param3': (float, 1e-16), 'param4': (str, "hello")}})
    with pytest.raises(AssertionError):
        inst = subckt('X1')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10')
    inst = subckt('X1', 'net10', 'net12')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'test_subckt'
    assert inst.pins == {'pin1': 'net10', 'pin2': 'net12'}
    assert inst.parameters == {'param1': 1, 'param2': 1e-3, 'param3': 1e-16, 'param4': 'hello'}

def test_circuit():
    TwoTerminalDevice = type('TwoTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b']})
    ThreeTerminalDevice = type('ThreeTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b', 'c']})
    ckt = Circuit()
    X1 = ckt.add_element(TwoTerminalDevice('X1', 'net1', 'net2'))
    X2 = ckt.add_element(ThreeTerminalDevice('X2', 'net1', 'net2', 'net3'))
    assert ckt.elements == [X1, X2]
    assert ckt.nets == ['net1', 'net2', 'net3']
    # Advanced graphx functionality test
    nodes = [X1, X2,
             'net1', 'net2', 'net3']
    assert all(x in ckt.nodes for x in nodes)
    assert all(x in nodes for x in ckt.nodes)
    edges = [# X1, net, pin
             (X1, 'net1', 'a'), (X1, 'net2', 'b'),
             ('net1', X1, 'a'), ('net2', X1, 'b'),
             # X2, net, pin
             (X2, 'net1', 'a'), (X2, 'net2', 'b'), (X2, 'net3', 'c'),
             ('net1', X2, 'a'), ('net2', X2, 'b'), ('net3', X2, 'c')]
    assert all(x in ckt.edges.data('pin') for x in edges), ckt.edges
    assert all(x in edges for x in ckt.edges.data('pin')), ckt.edges
