import pytest

from align.schema.subcircuit import Model, SubCircuit, Circuit, Instance
from align.schema.library import Library
from align.schema.types import set_context, Dict, String

@pytest.fixture
def library():
    library = Library()
    with set_context(library):
        model = Model(
            name='TwoTerminalDevice',
            pins=['A', 'B'],
            parameters={'MYPARAMETER': '3'})
    library.append(model)
    return library

@pytest.fixture
def test_ckt(library):
    with set_context(library):
        ckt = Circuit()
    return ckt

def test_subckt_definition(library, test_ckt):
    with set_context(library):
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['PIN1', 'PIN2'],
            parameters = {'PARAM1':1, 'PARAM2':'1E-3', 'PARAM3':'0.1F', 'PARAM4':'HELLO'})
        library.append(subckt)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='subckt',generator='Dummy')
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='subckt', pins={'PIN1': 'NET10'},generator='Dummy')
        inst = Instance(name='X1', model='subckt', pins={'PIN1': 'NET10', 'PIN2': 'NET12'},generator='Dummy')
    assert inst.name == 'X1'
    assert inst.model == 'SUBCKT'
    assert list(inst.pins.keys()) == ['PIN1', 'PIN2']
    assert list(inst.pins.values()) == ['NET10', 'NET12']
    assert inst.pins == {String('PIN1'): String('NET10'), String('PIN2'): 'NET12'}
    assert list(inst.parameters.keys()) == ['PARAM1', 'PARAM2', 'PARAM3', 'PARAM4']
    assert inst.parameters[String('PARAM1')] == '1'
    assert inst.parameters[String('PARAM2')] == '1E-3'
    assert inst.parameters[String('PARAM3')] == '0.1F'
    assert inst.parameters[String('PARAM4')] == 'HELLO'
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = subckt(name='X1', model='subckt', pins={'PIN1': 'NET10', 'PIN2': 'NET12'}, parameters={'garbage':''},generator='Dummy')
        inst = Instance(name='X1', model='subckt', pins={'PIN1': 'NET10', 'PIN2': 'NET12'}, parameters={'param1': '2', 'param3': '1e-16'},generator='Dummy')
    assert inst.parameters[String('PARAM1')] == '2'
    assert inst.parameters[String('PARAM3')] == '1E-16'

def test_subckt_instantiation(library, test_ckt):
    with set_context(library):
        subckt = SubCircuit(name='SUBCKT', pins=['PIN1', 'PIN2'], parameters={'PARAM1':1, 'PARAM2':1e-3, 'PARAM3':1E-16, 'PARAM4':"HELLO"})
        library.append(subckt)
    with set_context(subckt.elements):
        X1 = Instance(name='X1', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'},generator='Dummy')
        X2 = Instance(name='X2', model='TwoTerminalDevice', pins={'A': 'NET2', 'B': 'NET3'},generator='Dummy')
    subckt.elements.append(X1)
    subckt.elements.append(X2)
    assert subckt.elements == [X1, X2]
    assert subckt.elements[0] == X1
    assert subckt.elements[1] == X2
    assert subckt.get_element('x1') == X1
    assert subckt.nets == ['NET1', 'NET2', 'NET3']
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='subckt',generator='Dummy')
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='subckt', pins={'PIN1': 'NET10'},generator='Dummy')
        inst = Instance(name='X1', model='subckt', pins={'PIN1': 'NET10', 'PIN2': 'NET12'},generator='Dummy')
    assert inst.name == 'X1'
    assert inst.model == 'SUBCKT'
    assert isinstance(inst.pins, Dict)
    assert all(isinstance(x, String) for x in inst.pins.keys())
    assert all(isinstance(x, String) for x in inst.pins.values())
    assert inst.pins == {String('PIN1'): String('NET10'), String('PIN2'): String('NET12')}
    assert isinstance(inst.parameters, Dict)
    assert all(isinstance(x, String) for x in inst.parameters.keys())
    assert all(isinstance(x, String) for x in inst.parameters.values())
    assert inst.parameters == {String('PARAM1'): String('1'), String('PARAM2'): String('0.001'), String('PARAM3'): String('1E-16'), String('PARAM4'): String('HELLO')}
