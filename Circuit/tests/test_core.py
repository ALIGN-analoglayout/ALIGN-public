import pytest

from circuit.core import NTerminalDevice, Circuit, SubCircuit, Model

def test_n_terminal_device():
    inst = NTerminalDevice('X1')
    assert inst.name == 'X1'
    with pytest.raises(AssertionError):
        inst = NTerminalDevice('X2', 'net1')

@pytest.fixture
def TwoTerminalDevice():
    return type('TwoTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b']})

@pytest.fixture
def ThreeTerminalDevice():
    return type('ThreeTerminalDevice', (NTerminalDevice,), {'_pins': ['a', 'b', 'c'], '_parameters': {'myparameter': (int, 1)}})

def test_2_terminal_device(TwoTerminalDevice):
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

def test_3_terminal_device_w_parameter(ThreeTerminalDevice):
    with pytest.raises(AssertionError):
        inst = ThreeTerminalDevice('X1')
    with pytest.raises(AssertionError):
        inst = ThreeTerminalDevice('X1', 'net1')
    with pytest.raises(AssertionError):
        inst = ThreeTerminalDevice('X1', 'net1', 'net2')
    with pytest.raises(AssertionError):
        inst = ThreeTerminalDevice('X1', 'net1', 'net2', 'net3', garbageparameter=2)
    inst = ThreeTerminalDevice('X1', 'net1', 'net2', 'net3')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'ThreeTerminalDevice'
    assert inst.pins == {'a': 'net1', 'b': 'net2', 'c': 'net3'}
    assert inst.parameters == {'myparameter': 1}
    inst = ThreeTerminalDevice('X1', 'net1', 'net2', 'net3', myparameter = 2)
    assert inst.parameters == {'myparameter': 2}

def test_subckt_class(TwoTerminalDevice):
    subckt = SubCircuit('test_subckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3=1e-16, param4="hello")
    X1 = TwoTerminalDevice('X1', 'net1', 'net2')
    X2 = TwoTerminalDevice('X2', 'net2', 'net3')
    subckt.add_element(X1)
    subckt.add_element(X2)
    assert subckt.elements == [X1, X2]
    assert subckt.element('X1') == X1
    assert subckt.element('X2') == X2
    assert subckt.nets == ['net1', 'net2', 'net3']
    with pytest.raises(AssertionError):
        inst = subckt('X1')
    with pytest.raises(AssertionError):
        inst = subckt('X1', 'net10')
    inst = subckt('X1', 'net10', 'net12')
    assert inst.name == 'X1'
    assert type(inst).__name__ == 'test_subckt'
    assert inst.pins == {'pin1': 'net10', 'pin2': 'net12'}
    assert inst.parameters == {'param1': 1, 'param2': 1e-3, 'param3': 1e-16, 'param4': 'hello'}
    assert inst.elements == [X1, X2]
    assert inst.element('X1') == X1
    assert inst.element('X2') == X2
    assert inst.nets == ['net1', 'net2', 'net3']
    with pytest.raises(AssertionError):
        inst.add_element(TwoTerminalDevice('X3', 'net1', 'net3'))

def test_circuit(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    X1 = ckt.add_element(TwoTerminalDevice('X1', 'net1', 'net2'))
    X2 = ckt.add_element(ThreeTerminalDevice('X2', 'net1', 'net2', 'net3'))
    assert ckt.elements == [X1, X2]
    assert ckt.element('X1') == X1
    assert ckt.element('X2') == X2
    assert ckt.nets == ['net1', 'net2', 'net3']
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'net1', 'net2', 'net3']
    assert all(x in ckt.nodes for x in nodes)
    assert all(x in nodes for x in ckt.nodes)
    edges = [# X1, net, pin
             ('X1', 'net1', {'a'}), ('X1', 'net2', {'b'}),
             ('net1', 'X1', {'a'}), ('net2', 'X1', {'b'}),
             # X2, net, pin
             ('X2', 'net1', {'a'}), ('X2', 'net2', {'b'}), ('X2', 'net3', {'c'}),
             ('net1', 'X2', {'a'}), ('net2', 'X2', {'b'}), ('net3', 'X2', {'c'})]
    assert all(x in ckt.edges.data('pin') for x in edges), ckt.edges
    assert all(x in edges for x in ckt.edges.data('pin')), ckt.edges

def test_circuit_shared_net(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    X1 = ckt.add_element(TwoTerminalDevice('X1', 'net1', 'net2'))
    X2 = ckt.add_element(ThreeTerminalDevice('X2', 'net1', 'net1', 'net2'))
    assert ckt.elements == [X1, X2]
    assert ckt.element('X1') == X1
    assert ckt.element('X2') == X2
    assert ckt.nets == ['net1', 'net2']
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'net1', 'net2']
    assert all(x in ckt.nodes for x in nodes)
    assert all(x in nodes for x in ckt.nodes)
    edges = [# X1, net, pin
             ('X1', 'net1', {'a'}), ('X1', 'net2', {'b'}),
             ('net1', 'X1', {'a'}), ('net2', 'X1', {'b'}),
             # X2, net, pin
             ('X2', 'net1', {'a', 'b'}), ('X2', 'net2', {'c'}),
             ('net1', 'X2', {'a', 'b'}), ('net2', 'X2', {'c'})]
    assert all(x in ckt.edges.data('pin') for x in edges), ckt.edges
    assert all(x in edges for x in ckt.edges.data('pin')), ckt.edges

def test_model(ThreeTerminalDevice):
    CustomDevice = Model('CustomDevice', ThreeTerminalDevice, newparam=1, newparam2='hello')
    with pytest.raises(AssertionError):
        inst = CustomDevice('X1', 'net01', 'net02', 'net03', garbage=2)
    inst = CustomDevice('X1', 'net01', 'net02', 'net03', myparameter=2, newparam=2)
    assert type(inst).__name__ == 'CustomDevice'
    assert inst.pins == {'a': 'net01', 'b': 'net02', 'c': 'net03'}
    assert inst.parameters == {'myparameter': 2, 'newparam': 2, 'newparam2': 'hello'}

@pytest.fixture
def simple_netlist(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    CustomDevice = Model('CustomDevice', ThreeTerminalDevice, newparam=1, newparam2='hello')
    ckt.add_element(CustomDevice('X1', 'net1', 'in1', 'net01'))
    ckt.add_element(CustomDevice('X2', 'net2', 'in2', 'net02'))
    ckt.add_element(CustomDevice('X3', 'net3', 'net1', 'net1'))
    ckt.add_element(CustomDevice('X4', 'net3', 'net1', 'net2'))
    ckt.add_element(TwoTerminalDevice('X5', 'net01', 'net00'))
    ckt.add_element(TwoTerminalDevice('X6', 'net02', 'net00'))
    ckt.add_element(TwoTerminalDevice('X7', 'net3', 'net03'))
    return ckt

@pytest.fixture
def matching_subckt(ThreeTerminalDevice):
    subckt = SubCircuit('test_subckt', 'pin1', 'pin2', 'pin3')
    subckt.add_element(ThreeTerminalDevice('X1', 'pin3', 'pin1', 'pin1'))
    subckt.add_element(ThreeTerminalDevice('X2', 'pin3', 'pin1', 'pin2'))
    return subckt

def test_find_matching_subgraphs(simple_netlist, matching_subckt, ThreeTerminalDevice, TwoTerminalDevice):
    ckt, subckt = simple_netlist, matching_subckt
    # Validate true match
    assert len(ckt.find_matching_subgraphs(subckt)) == 1
    assert ckt.find_matching_subgraphs(subckt)[0] == {'X3': 'X1', 'net3': 'pin3', 'net1': 'pin1', 'X4': 'X2', 'net2': 'pin2'}
    # Validate false match
    subckt2 = SubCircuit('test_subckt2', 'pin1', 'pin2', 'pin3', 'pin4', 'pin5')
    subckt2.add_element(ThreeTerminalDevice('X1', 'pin1', 'pin3', 'pin4'))
    subckt2.add_element(ThreeTerminalDevice('X2', 'pin2', 'pin3', 'pin5'))
    assert len(ckt.find_matching_subgraphs(subckt2)) == 0
    # Validate overtly aggressive match. 3 of 4 matches are probably useless from a circuit standpoint
    subckt3 = SubCircuit('test_subckt3', 'pin1', 'pin2', 'pin3', 'pin4')
    subckt3.add_element(TwoTerminalDevice('X1', 'pin1', 'pin2'))
    subckt3.add_element(TwoTerminalDevice('X2', 'pin3', 'pin4'))
    assert len(ckt.find_matching_subgraphs(subckt3)) == 4

def test_replace_matching_subgraphs(simple_netlist, matching_subckt):
    ckt, subckt = simple_netlist, matching_subckt
    matches = [{'X3': 'X1', 'net3': 'pin3', 'net1': 'pin1', 'X4': 'X2', 'net2': 'pin2'}]
    ckt.replace_matching_subgraphs(subckt)
    assert all(x not in ckt.nodes for x in matches[0].keys() if x.startswith('X'))
    assert 'X_test_subckt_0' in ckt.nodes
    new_edges = [('X_test_subckt_0', 'net3', {'pin3'}), ('X_test_subckt_0', 'net1', {'pin1'}), ('X_test_subckt_0', 'net2', {'pin2'})]
    assert all(x in ckt.edges.data('pin') for x in new_edges)
