import pytest

from align.schema.subcircuit import Model, SubCircuit, Instance

@pytest.fixture
def TwoTerminalDevice():
    return Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={'MYPARAMETER': '3'})

def test_subckt_definition():
    subckt = SubCircuit(
        name = 'TEST_SUBCKT',
        pins = ['PIN1', 'PIN2'],
        parameters = {'PARAM1':1, 'PARAM2':'1E-3', 'PARAM3':'0.1F', 'PARAM4':'HELLO'})
    with pytest.raises(Exception):
        inst = Instance(name='X1', model=subckt)
    with pytest.raises(Exception):
        inst = Instance(name='X1', model=subckt, pins={'PIN1': 'NET10'})
    inst = Instance(name='X1', model=subckt, pins={'PIN1': 'NET10', 'PIN2': 'NET12'})
    assert inst.name == 'X1'
    assert inst.model.name == 'TEST_SUBCKT'
    assert inst.pins == {'PIN1': 'NET10', 'PIN2': 'NET12'}
    assert list(inst.parameters.keys()) == ['PARAM1', 'PARAM2', 'PARAM3', 'PARAM4']
    assert inst.parameters['PARAM1'] == '1'
    assert inst.parameters['PARAM2'] == '1E-3'
    assert inst.parameters['PARAM3'] == '0.1F'
    assert inst.parameters['PARAM4'] == 'HELLO'
    with pytest.raises(Exception):
        inst = subckt(name='X1', model=subckt, pins={'PIN1': 'NET10', 'PIN2': 'NET12'}, parameters={'garbage':''})
    inst = Instance(name='X1', model=subckt, pins={'PIN1': 'NET10', 'PIN2': 'NET12'}, parameters={'param1': '2', 'param3': '1e-16'})
    assert inst.parameters['PARAM1'] == '2'
    assert inst.parameters['PARAM3'] == '1E-16'

def test_subckt_instantiation(TwoTerminalDevice):
    subckt = SubCircuit(name='TEST_SUBCKT', pins=['PIN1', 'PIN2'], parameters={'PARAM1':1, 'PARAM2':1e-3, 'PARAM3':1E-16, 'PARAM4':"HELLO"})
    X1 = Instance(name='X1', model=TwoTerminalDevice, pins={'A': 'NET1', 'B': 'NET2'})
    X2 = Instance(name='X2', model=TwoTerminalDevice, pins={'A': 'NET2', 'B': 'NET3'})
    subckt.add(X1)
    subckt.add(X2)
    assert subckt.elements == [X1, X2]
    assert subckt.elements[0] == X1
    assert subckt.elements[1] == X2
    assert subckt.nets == ['NET1', 'NET2', 'NET3']
    with pytest.raises(Exception):
        inst = subckt('X1')
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10')
    inst = Instance(name='X1', model=subckt, pins={'PIN1': 'NET10', 'PIN2': 'NET12'})
    assert inst.name == 'X1'
    assert inst.model.name == 'TEST_SUBCKT'
    assert inst.pins == {'PIN1': 'NET10', 'PIN2': 'NET12'}
    assert inst.parameters == {'PARAM1': '1', 'PARAM2': '0.001', 'PARAM3': '1E-16', 'PARAM4': 'HELLO'}
    assert inst.model.elements == [X1, X2]
    assert inst.model.elements[0] == X1
    assert inst.model.elements[1] == X2
    assert inst.model.nets == ['NET1', 'NET2', 'NET3']

