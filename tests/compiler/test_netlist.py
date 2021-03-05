import pytest
import pathlib

from align.circuit.model import Model
from align.circuit.subcircuit import SubCircuit, Circuit
from align.circuit.parser import SpiceParser

from align.compiler.netlist import Netlist

@pytest.fixture
def circuit():
    return Circuit()

@pytest.fixture
def netlist(circuit):
    return Netlist(circuit)

@pytest.fixture
def TwoTerminalDevice():
    return Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={'MYPARAMETER': '3'})

@pytest.fixture
def ThreeTerminalDevice():
    return Model(name='ThreeTerminalDevice', pins=['A', 'B', 'C'], parameters={'MYPARAMETER': '1'})

@pytest.fixture
def simple_circuit(TwoTerminalDevice, ThreeTerminalDevice, circuit):
    CustomDevice = Model(name='CustomDevice', base=ThreeTerminalDevice, parameters={'myparameter':1})
    circuit.add(CustomDevice('X1', 'NET1', 'in1', 'net01'))
    circuit.add(CustomDevice('X2', 'NET2', 'in2', 'net02'))
    circuit.add(CustomDevice('X3', 'NET3', 'NET1', 'NET1'))
    circuit.add(CustomDevice('X4', 'NET3', 'NET1', 'NET2'))
    circuit.add(TwoTerminalDevice('X5', 'net01', 'net00'))
    circuit.add(TwoTerminalDevice('X6', 'net02', 'net00'))
    circuit.add(TwoTerminalDevice('X7', 'NET3', 'net03'))
    return circuit

@pytest.fixture
def matching_subckt(ThreeTerminalDevice):
    subckt = SubCircuit(name='TEST_SUBCKT', pins=['PIN1', 'PIN2', 'PIN3'], parameters={'MYPARAMETER':1})
    subckt.add(ThreeTerminalDevice('X1', 'PIN3', 'PIN1', 'PIN1', MYPARAMETER=1))
    subckt.add(ThreeTerminalDevice('X2', 'PIN3', 'PIN1', 'PIN2', MYPARAMETER='MYPARAMETER'))
    return subckt

@pytest.fixture
def heirarchical_ckt(matching_subckt, ThreeTerminalDevice, circuit):
    ckt = circuit
    subckt = SubCircuit(name='parent_subckt', pins=['PIN1', 'PIN2'])
    subckt.add(matching_subckt('X1', 'PIN1', 'PIN2', 'NET1', MYPARAMETER='2'))
    subckt.add(ThreeTerminalDevice('X2', 'NET1', 'PIN1', 'PIN2', MYPARAMETER='1'))
    ckt.add(subckt('XSUB1', 'NET1', 'NET2'))
    ckt.add(matching_subckt('XSUB2', 'NET1', 'NET2', 'NET3', MYPARAMETER='3'))
    return ckt

@pytest.fixture
def ota():
    parser = SpiceParser()
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'ota.cir').resolve()) as fp:
        parser.parse(fp.read())
    # Extract ckt
    return parser.library['OTA']

@pytest.fixture
def primitives():
    # parse subckts
    parser = SpiceParser()
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'basic_template.sp').resolve()) as fp:
        parser.parse(fp.read())
    return [v for v in parser.library.values() if isinstance(v, SubCircuit)]

def test_netlist(TwoTerminalDevice, ThreeTerminalDevice, circuit):
    X1 = circuit.add(TwoTerminalDevice('X1', 'NET1', 'NET2'))
    X2 = circuit.add(ThreeTerminalDevice('X2', 'NET1', 'NET2', 'NET3'))
    netlist = Netlist(circuit)
    assert netlist.elements == circuit.elements
    assert netlist.nets == circuit.nets
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'NET1', 'NET2', 'NET3']
    assert all(x in netlist.nodes for x in nodes)
    assert all(x in nodes for x in netlist.nodes)
    edges = [# X1, net, pin
             ('X1', 'NET1', {'A'}), ('X1', 'NET2', {'B'}),
             ('NET1', 'X1', {'A'}), ('NET2', 'X1', {'B'}),
             # X2, net, pin
             ('X2', 'NET1', {'A'}), ('X2', 'NET2', {'B'}), ('X2', 'NET3', {'C'}),
             ('NET1', 'X2', {'A'}), ('NET2', 'X2', {'B'}), ('NET3', 'X2', {'C'})]
    assert all(x in netlist.edges.data('pin') for x in edges), netlist.edges
    assert all(x in edges for x in netlist.edges.data('pin')), netlist.edges

def test_netlist_shared_net(TwoTerminalDevice, ThreeTerminalDevice, circuit):
    X1 = circuit.add(TwoTerminalDevice('X1', 'NET1', 'NET2'))
    X2 = circuit.add(ThreeTerminalDevice('X2', 'NET1', 'NET1', 'NET2'))
    netlist = Netlist(circuit)
    assert netlist.elements == circuit.elements
    assert netlist.nets == circuit.nets
    # Advanced graphx functionality test
    nodes = ['X1', 'X2',
             'NET1', 'NET2']
    assert all(x in netlist.nodes for x in nodes)
    assert all(x in nodes for x in netlist.nodes)
    edges = [# X1, net, pin
             ('X1', 'NET1', {'A'}), ('X1', 'NET2', {'B'}),
             ('NET1', 'X1', {'A'}), ('NET2', 'X1', {'B'}),
             # X2, net, pin
             ('X2', 'NET1', {'A', 'B'}), ('X2', 'NET2', {'C'}),
             ('NET1', 'X2', {'A', 'B'}), ('NET2', 'X2', {'C'})]
    assert all(x in netlist.edges.data('pin') for x in edges), netlist.edges
    assert all(x in edges for x in netlist.edges.data('pin')), netlist.edges

def test_find_subgraph_matches(simple_circuit, matching_subckt, ThreeTerminalDevice, TwoTerminalDevice):
    netlist, matching_netlist = Netlist(simple_circuit), Netlist(matching_subckt)
    # Validate true match
    assert len(netlist.find_subgraph_matches(matching_netlist)) == 1
    assert netlist.find_subgraph_matches(matching_netlist)[0] == {'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}
    # Validate false match
    subckt2 = SubCircuit(name='test_subckt2', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4', 'PIN5'])
    subckt2.add(ThreeTerminalDevice('X1', 'PIN1', 'PIN3', 'PIN4'))
    subckt2.add(ThreeTerminalDevice('X2', 'PIN2', 'PIN3', 'PIN5'))
    assert len(netlist.find_subgraph_matches(Netlist(subckt2))) == 0
    # Validate filtering of redundant subgraphs (There are 4 matches. Only 1 should be returned)
    subckt3 = SubCircuit(name='test_subckt3', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4'])
    subckt3.add(TwoTerminalDevice('X1', 'PIN1', 'PIN2'))
    subckt3.add(TwoTerminalDevice('X2', 'PIN3', 'PIN4'))
    assert len(netlist.find_subgraph_matches(Netlist(subckt3))) == 1

def test_replace_matching_subgraph(simple_circuit, matching_subckt):
    netlist, matching_netlist = Netlist(simple_circuit), Netlist(matching_subckt)
    matches = [{'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}]
    netlist.replace_matching_subgraph(matching_netlist)
    assert all(x not in netlist.nodes for x in matches[0].keys() if x.startswith('X'))
    assert 'X_TEST_SUBCKT_0' in netlist.nodes
    new_edges = [('X_TEST_SUBCKT_0', 'NET3', {'PIN3'}), ('X_TEST_SUBCKT_0', 'NET1', {'PIN1'}), ('X_TEST_SUBCKT_0', 'NET2', {'PIN2'})]
    assert all(x in netlist.edges.data('pin') for x in new_edges), netlist.edges.data('pin')

def test_replace_repeated_subckts(ota):
    # parse netlist
    netlist = Netlist(ota)
    netlist.flatten()
    subckts = netlist.replace_repeated_subckts()
    assert len(subckts) == 1
    assert len(subckts[0].elements) == 4
    elements = {x.name for x in subckts[0].elements}
    assert elements == {'M10', 'M7', 'M9', 'M1'} or elements == {'M2', 'M6', 'M8', 'M0'}

def test_replace_matching_subckts(ota, primitives):
    ckt = ota
    # Extract ckt
    netlist = Netlist(ckt)
    netlist.flatten()
    # Sort subckts using hypothetical complexity cost
    primitives.sort(key=lambda x: len(x.elements)*10000 - 100 * len(x.pins) + len(x.nets), reverse=True)
    assert len(ckt.elements) == 10
    assert all(x.name.startswith('M') for x in ckt.elements)
    # Perform subgraph matching & replacement
    for subckt in primitives:
        netlist.replace_matching_subgraph(Netlist(subckt))
    assert len(ckt.elements) == 5
    assert all(x.name.startswith('X') for x in ckt.elements)

def test_flatten(heirarchical_ckt):
    ckt = heirarchical_ckt
    netlist = Netlist(ckt)
    netlist.flatten()
    myparametermap = {
        'XSUB1_X2': '1',
        'XSUB1_X1_X1': '1',
        'XSUB1_X1_X2': '2',
        'XSUB2_X1': '1',
        'XSUB2_X2': '3'
    }
    assert {x.name for x in ckt.elements} == set(myparametermap.keys())
    assert set(ckt.nets) == {'NET1', 'NET2', 'NET3', 'XSUB1_NET1'}
    assert all(element.parameters['MYPARAMETER'] == myparametermap[element.name] for element in ckt.elements)

def test_flatten_depth1(heirarchical_ckt):
    ckt = heirarchical_ckt
    netlist = Netlist(ckt)
    netlist.flatten(1)
    myparametermap = {
        'XSUB1_X2': '1',
        'XSUB1_X1': '2',
        'XSUB2_X1': '1',
        'XSUB2_X2': '3'
    }
    assert {x.name for x in ckt.elements} == set(myparametermap.keys())
    assert set(ckt.nets) == {'NET1', 'NET2', 'NET3', 'XSUB1_NET1'}
    assert all(element.parameters['MYPARAMETER'] == myparametermap[element.name] for element in ckt.elements)
