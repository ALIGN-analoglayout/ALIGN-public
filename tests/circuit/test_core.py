import pytest

from align.circuit.core import Model, Circuit, SubCircuit
from align.circuit.library import Library

library = Library('dummy')

@pytest.fixture
def TwoTerminalDevice():
    return Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={'MYPARAMETER': '3'}, library=library)

@pytest.fixture
def ThreeTerminalDevice():
    return Model(name='ThreeTerminalDevice', pins=['A', 'B', 'C'], parameters={'MYPARAMETER': '1'}, library=library)

def test_subckt_class(TwoTerminalDevice):
    subckt = SubCircuit(name='TEST_SUBCKT', pins=['PIN1', 'PIN2'], parameters={'PARAM1':1, 'PARAM2':1e-3, 'PARAM3':1E-16, 'PARAM4':"HELLO"}, library=library)
    X1 = TwoTerminalDevice('X1', 'NET1', 'NET2')
    X2 = TwoTerminalDevice('X2', 'NET2', 'NET3')
    subckt.add_element(X1)
    subckt.add_element(X2)
    assert subckt.elements == [X1, X2]
    assert subckt.element('X1') == X1
    assert subckt.element('X2') == X2
    assert subckt.nets == ['NET1', 'NET2', 'NET3']
    with pytest.raises(Exception):
        inst = subckt('X1')
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10')
    inst = subckt('X1', 'NET10', 'NET12')
    assert inst.name == 'X1'
    assert inst.model.name == 'TEST_SUBCKT'
    assert inst.pins == {'PIN1': 'NET10', 'PIN2': 'NET12'}
    assert inst.parameters == {'PARAM1': '1', 'PARAM2': '0.001', 'PARAM3': '1E-16', 'PARAM4': 'HELLO'}
    assert inst.model.circuit.elements == [X1, X2]
    assert inst.model.circuit.element('X1') == X1
    assert inst.model.circuit.element('X2') == X2
    assert inst.model.circuit.nets == ['NET1', 'NET2', 'NET3']

def test_circuit(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    X1 = ckt.add_element(TwoTerminalDevice('X1', 'NET1', 'NET2'))
    X2 = ckt.add_element(ThreeTerminalDevice('X2', 'NET1', 'NET2', 'NET3'))
    assert ckt.elements == [X1, X2]
    assert ckt.element('X1') == X1
    assert ckt.element('X2') == X2
    assert ckt.nets == ['NET1', 'NET2', 'NET3']
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'NET1', 'NET2', 'NET3']
    assert all(x in ckt.nodes for x in nodes)
    assert all(x in nodes for x in ckt.nodes)
    edges = [# X1, net, pin
             ('X1', 'NET1', {'A'}), ('X1', 'NET2', {'B'}),
             ('NET1', 'X1', {'A'}), ('NET2', 'X1', {'B'}),
             # X2, net, pin
             ('X2', 'NET1', {'A'}), ('X2', 'NET2', {'B'}), ('X2', 'NET3', {'C'}),
             ('NET1', 'X2', {'A'}), ('NET2', 'X2', {'B'}), ('NET3', 'X2', {'C'})]
    assert all(x in ckt.edges.data('pin') for x in edges), ckt.edges
    assert all(x in edges for x in ckt.edges.data('pin')), ckt.edges

def test_circuit_shared_net(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    X1 = ckt.add_element(TwoTerminalDevice('X1', 'NET1', 'NET2'))
    X2 = ckt.add_element(ThreeTerminalDevice('X2', 'NET1', 'NET1', 'NET2'))
    assert ckt.elements == [X1, X2]
    assert ckt.element('X1') == X1
    assert ckt.element('X2') == X2
    assert ckt.nets == ['NET1', 'NET2']
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'NET1', 'NET2']
    assert all(x in ckt.nodes for x in nodes)
    assert all(x in nodes for x in ckt.nodes)
    edges = [# X1, net, pin
             ('X1', 'NET1', {'A'}), ('X1', 'NET2', {'B'}),
             ('NET1', 'X1', {'A'}), ('NET2', 'X1', {'B'}),
             # X2, net, pin
             ('X2', 'NET1', {'A', 'B'}), ('X2', 'NET2', {'C'}),
             ('NET1', 'X2', {'A', 'B'}), ('NET2', 'X2', {'C'})]
    assert all(x in ckt.edges.data('pin') for x in edges), ckt.edges
    assert all(x in edges for x in ckt.edges.data('pin')), ckt.edges

@pytest.fixture
def simple_netlist(TwoTerminalDevice, ThreeTerminalDevice):
    ckt = Circuit()
    CustomDevice = Model(name='CustomDevice', base='ThreeTerminalDevice', parameters={'myparameter':1}, library=library)
    ckt.add_element(CustomDevice('X1', 'NET1', 'in1', 'net01'))
    ckt.add_element(CustomDevice('X2', 'NET2', 'in2', 'net02'))
    ckt.add_element(CustomDevice('X3', 'NET3', 'NET1', 'NET1'))
    ckt.add_element(CustomDevice('X4', 'NET3', 'NET1', 'NET2'))
    ckt.add_element(TwoTerminalDevice('X5', 'net01', 'net00'))
    ckt.add_element(TwoTerminalDevice('X6', 'net02', 'net00'))
    ckt.add_element(TwoTerminalDevice('X7', 'NET3', 'net03'))
    return ckt

@pytest.fixture
def matching_subckt(ThreeTerminalDevice):
    subckt = SubCircuit(name='TEST_SUBCKT', pins=['PIN1', 'PIN2', 'PIN3'], parameters={'MYPARAMETER':1}, library=library)
    subckt.add_element(ThreeTerminalDevice('X1', 'PIN3', 'PIN1', 'PIN1', MYPARAMETER=1))
    subckt.add_element(ThreeTerminalDevice('X2', 'PIN3', 'PIN1', 'PIN2', MYPARAMETER='MYPARAMETER'))
    return subckt

def test_find_subgraph_matches(simple_netlist, matching_subckt, ThreeTerminalDevice, TwoTerminalDevice):
    ckt, subckt = simple_netlist, matching_subckt
    # Validate true match
    assert len(ckt.find_subgraph_matches(subckt.circuit)) == 1
    assert ckt.find_subgraph_matches(subckt.circuit)[0] == {'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}
    # Validate false match
    subckt2 = SubCircuit(name='test_subckt2', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4', 'PIN5'], library=library)
    subckt2.add_element(ThreeTerminalDevice('X1', 'PIN1', 'PIN3', 'PIN4'))
    subckt2.add_element(ThreeTerminalDevice('X2', 'PIN2', 'PIN3', 'PIN5'))
    assert len(ckt.find_subgraph_matches(subckt2.circuit)) == 0
    # Validate filtering of redundant subgraphs (There are 4 matches. Only 1 should be returned)
    subckt3 = SubCircuit(name='test_subckt3', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4'], library=library)
    subckt3.add_element(TwoTerminalDevice('X1', 'PIN1', 'PIN2'))
    subckt3.add_element(TwoTerminalDevice('X2', 'PIN3', 'PIN4'))
    assert len(ckt.find_subgraph_matches(subckt3.circuit)) == 1

def test_replace_matching_subgraphs(simple_netlist, matching_subckt):
    ckt, subckt = simple_netlist, matching_subckt
    matches = [{'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}]
    ckt.replace_matching_subckts(subckt)
    print(ckt.xyce())
    print(subckt.xyce())
    assert all(x not in ckt.nodes for x in matches[0].keys() if x.startswith('X'))
    assert 'X_TEST_SUBCKT_0' in ckt.nodes
    new_edges = [('X_TEST_SUBCKT_0', 'NET3', {'PIN3'}), ('X_TEST_SUBCKT_0', 'NET1', {'PIN1'}), ('X_TEST_SUBCKT_0', 'NET2', {'PIN2'})]
    assert all(x in ckt.edges.data('pin') for x in new_edges), ckt.edges.data('pin')

@pytest.fixture
def heirarchical_ckt(matching_subckt, ThreeTerminalDevice):
    ckt = Circuit()
    subckt = SubCircuit(name='parent_subckt', pins=['PIN1', 'PIN2'], library=library)
    subckt.add_element(matching_subckt('X1', 'PIN1', 'PIN2', 'NET1', MYPARAMETER='2'))
    subckt.add_element(ThreeTerminalDevice('X2', 'NET1', 'PIN1', 'PIN2', MYPARAMETER='1'))
    ckt.add_element(subckt('XSUB1', 'NET1', 'NET2'))
    ckt.add_element(matching_subckt('XSUB2', 'NET1', 'NET2', 'NET3', MYPARAMETER='3'))
    return ckt

def test_flatten(heirarchical_ckt):
    ckt = heirarchical_ckt
    ckt.flatten()
    myparametermap = {
        'XSUB1_X2': '1',
        'XSUB1_X1_X1': '1',
        'XSUB1_X1_X2': '2',
        'XSUB2_X1': '1',
        'XSUB2_X2': '3'
    }
    assert {x.name for x in ckt.elements} == set(myparametermap.keys())
    assert set(ckt.nets) == {'NET1', 'NET2', 'NET3', 'XSUB1_NET1'}
    assert all(ckt.element(elem).parameters['MYPARAMETER'] == param for elem, param in myparametermap.items()), [ckt.element(elem).parameters['MYPARAMETER'] for elem in myparametermap.keys()]

def test_flatten_depth1(heirarchical_ckt):
    ckt = heirarchical_ckt
    ckt.flatten(1)
    myparametermap = {
        'XSUB1_X2': '1',
        'XSUB1_X1': '2',
        'XSUB2_X1': '1',
        'XSUB2_X2': '3'
    }
    assert {x.name for x in ckt.elements} == set(myparametermap.keys())
    assert set(ckt.nets) == {'NET1', 'NET2', 'NET3', 'XSUB1_NET1'}
    assert all(ckt.element(elem).parameters['MYPARAMETER'] == param for elem, param in myparametermap.items()), [ckt.element(elem).parameters['MYPARAMETER'] for elem in myparametermap.keys()]
