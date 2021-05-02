import pytest
import pathlib

from align.schema.library import Library
from align.schema.model import Model
from align.schema.instance import Instance
from align.schema.subcircuit import SubCircuit, Circuit
from align.schema.parser import SpiceParser
from align.schema.graph import Graph
from align.schema.types import set_context

@pytest.fixture
def library():
    library = Library(loadbuiltins=True)
    with set_context(library):
        library.append(Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={'MYPARAMETER': '3'}))
        library.append(Model(name='ThreeTerminalDevice', pins=['A', 'B', 'C'], parameters={'MYPARAMETER': '1'}))
    return library

@pytest.fixture
def circuit(library):
    with set_context(library):
        ckt = Circuit()
    return ckt

@pytest.fixture
def simple_circuit(circuit):
    with set_context(circuit.parent):
        circuit.parent.append(Model(name='CustomDevice', base='ThreeTerminalDevice', parameters={'myparameter':1}))
    with set_context(circuit.elements):
        circuit.elements.append(Instance(name='X1', model='CustomDevice', pins={'A': 'NET1', 'B': 'in1', 'C': 'net01'}))
        circuit.elements.append(Instance(name='X2', model='CustomDevice', pins={'A': 'NET2', 'B': 'in2', 'C': 'net02'}))
        circuit.elements.append(Instance(name='X3', model='CustomDevice', pins={'A': 'NET3', 'B': 'NET1', 'C': 'NET1'}))
        circuit.elements.append(Instance(name='X4', model='CustomDevice', pins={'A': 'NET3', 'B': 'NET1', 'C': 'NET2'}))
        circuit.elements.append(Instance(name='X5', model='TwoTerminalDevice', pins={'A':'net01', 'B':'net00'}))
        circuit.elements.append(Instance(name='X6', model='TwoTerminalDevice', pins={'A':'net02', 'B':'net00'}))
        circuit.elements.append(Instance(name='X7', model='TwoTerminalDevice', pins={'A':'NET3', 'B':'net03'}))
    return circuit

@pytest.fixture
def matching_subckt(library):
    with set_context(library):
        subckt = SubCircuit(name='TEST_SUBCKT', pins=['PIN1', 'PIN2', 'PIN3'], parameters={'MYPARAMETER':1})
    library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='X1', model='ThreeTerminalDevice', pins={'A': 'PIN3', 'B': 'PIN1', 'C': 'PIN1'}, parameters={'MYPARAMETER': 1}))
        subckt.elements.append(Instance(name='X2', model='ThreeTerminalDevice', pins={'A': 'PIN3', 'B': 'PIN1', 'C': 'PIN2'}, parameters={'MYPARAMETER': 'MYPARAMETER'}))
    return subckt

@pytest.fixture
def heirarchical_ckt(matching_subckt):
    with set_context(matching_subckt.parent):
        ckt = Circuit()
        subckt = SubCircuit(name='PARENT_SUBCKT', pins=['PIN1', 'PIN2'])
    matching_subckt.parent.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(
            name='X1',
            model='TEST_SUBCKT',
            pins={'PIN1': 'PIN1', 'PIN2': 'PIN2', 'PIN3': 'NET1'},
            parameters={'MYPARAMETER': '2'}))
        subckt.elements.append(Instance(
            name='X2',
            model='ThreeTerminalDevice',
            pins={'A': 'NET1', 'B': 'PIN1', 'C': 'PIN2'},
            parameters={'MYPARAMETER': '1'}))
    with set_context(ckt.elements):
        ckt.elements.append(Instance(
            name='XSUB1',
            model='PARENT_SUBCKT',
            pins={'PIN1': 'NET1', 'PIN2': 'NET2'}))
        ckt.elements.append(Instance(
            name='XSUB2',
            model='TEST_SUBCKT',
            pins={'PIN1': 'NET1', 'PIN2': 'NET2', 'PIN3': 'NET3'},
            parameters={'MYPARAMETER': '3'}))
    return ckt

@pytest.fixture
def ota():
    parser = SpiceParser()
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'ota.cir').resolve()) as fp:
        parser.parse(fp.read())
    # Extract ckt
    return parser.library.find('OTA')

@pytest.fixture
def primitives():
    # parse subckts
    parser = SpiceParser()
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'basic_template.sp').resolve()) as fp:
        parser.parse(fp.read())
    return [v for v in parser.library if isinstance(v, SubCircuit)]

def test_netlist(circuit):
    with set_context(circuit.elements):
        X1 = circuit.elements.append(Instance(name='X1', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'}))
        X2 = circuit.elements.append(Instance(name='X2', model='ThreeTerminalDevice', pins={'A': 'NET1', 'B': 'NET2', 'C': 'NET3'}))
    netlist = Graph(circuit)
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

def test_netlist_shared_net(circuit):
    with set_context(circuit.elements):
        X1 = circuit.elements.append(Instance(name='X1', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'}))
        X2 = circuit.elements.append(Instance(name='X2', model='ThreeTerminalDevice', pins={'A': 'NET1', 'B': 'NET1', 'C': 'NET2'}))
    netlist = Graph(circuit)
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

def test_find_subgraph_matches(simple_circuit, matching_subckt):
    netlist, matching_netlist = Graph(simple_circuit), Graph(matching_subckt)
    # Validate true match
    assert len(netlist.find_subgraph_matches(matching_netlist)) == 1
    assert netlist.find_subgraph_matches(matching_netlist)[0] == {'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}
    # Validate false match
    with set_context(simple_circuit.parent):
        subckt2 = SubCircuit(name='test_subckt2', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4', 'PIN5'])
    with set_context(subckt2.elements):
        subckt2.elements.append(Instance(name='X1', model='ThreeTerminalDevice', pins={'A': 'PIN1', 'B': 'PIN3', 'C': 'PIN4'}))
        subckt2.elements.append(Instance(name='X2', model='ThreeTerminalDevice', pins={'A': 'PIN2', 'B': 'PIN3', 'C': 'PIN5'}))
    assert len(netlist.find_subgraph_matches(Graph(subckt2))) == 0
    # Validate filtering of redundant subgraphs (There are 4 matches. Only 1 should be returned)
    with set_context(simple_circuit.parent):
        subckt3 = SubCircuit(name='test_subckt3', pins=['PIN1', 'PIN2', 'PIN3', 'PIN4'])
    with set_context(subckt3.elements):
        subckt3.elements.append(Instance(name='X1', model='TwoTerminalDevice', pins={'A': 'PIN1', 'B': 'PIN2'}))
        subckt3.elements.append(Instance(name='X2', model='TwoTerminalDevice', pins={'A': 'PIN3', 'B': 'PIN4'}))
    assert len(netlist.find_subgraph_matches(Graph(subckt3))) == 1

def test_replace_matching_subgraph(simple_circuit, matching_subckt):
    netlist, matching_netlist = Graph(simple_circuit), Graph(matching_subckt)
    matches = [{'X3': 'X1', 'NET3': 'PIN3', 'NET1': 'PIN1', 'X4': 'X2', 'NET2': 'PIN2'}]
    netlist.replace_matching_subgraph(matching_netlist)
    assert all(x not in netlist.nodes for x in matches[0].keys() if x.startswith('X'))
    assert 'X_TEST_SUBCKT_0' in netlist.nodes
    new_edges = [('X_TEST_SUBCKT_0', 'NET3', {'PIN3'}), ('X_TEST_SUBCKT_0', 'NET1', {'PIN1'}), ('X_TEST_SUBCKT_0', 'NET2', {'PIN2'})]
    assert all(x in netlist.edges.data('pin') for x in new_edges), netlist.edges.data('pin')

def test_replace_repeated_subckts(ota):
    # parse netlist
    netlist = Graph(ota)
    netlist.flatten()
    subckts = netlist.replace_repeated_subckts()
    assert len(subckts) == 1
    assert len(subckts[0].elements) == 4
    elements = {x.name for x in subckts[0].elements}
    assert elements == {'M10', 'M7', 'M9', 'M1'} or elements == {'M2', 'M6', 'M8', 'M0'}

def test_replace_matching_subckts(ota, primitives):
    ckt = ota
    # Extract ckt
    netlist = Graph(ckt)
    netlist.flatten()
    # Sort subckts using hypothetical complexity cost
    primitives.sort(key=lambda x: len(x.elements)*10000 - 100 * len(x.pins) + len(x.nets), reverse=True)
    assert len(ckt.elements) == 10
    assert all(x.name.startswith('M') for x in ckt.elements)
    # Perform subgraph matching & replacement
    for subckt in primitives:
        netlist.replace_matching_subgraph(Graph(subckt))
    assert len(ckt.elements) == 5
    assert all(x.name.startswith('X') for x in ckt.elements)

def test_flatten(heirarchical_ckt):
    ckt = heirarchical_ckt
    netlist = Graph(ckt)
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
    netlist = Graph(ckt)
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
