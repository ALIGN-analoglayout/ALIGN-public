import pytest

from align.circuit.subcircuit import SubCircuit

def test_subckt():
    subckt = SubCircuit(
        name = 'TEST_SUBCKT',
        pins = ['PIN1', 'PIN2'],
        parameters = {'PARAM1':1, 'PARAM2':'1E-3', 'PARAM3':'0.1F', 'PARAM4':'HELLO'})
    with pytest.raises(Exception):
        inst = subckt('X1')
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10')
    inst = subckt('X1', 'NET10', 'NET12')
    assert inst.name == 'X1'
    assert inst.model.name == 'TEST_SUBCKT'
    assert inst.pins == {'PIN1': 'NET10', 'PIN2': 'NET12'}
    assert list(inst.parameters.keys()) == ['PARAM1', 'PARAM2', 'PARAM3', 'PARAM4']
    assert inst.parameters['PARAM1'] == '1'
    assert inst.parameters['PARAM2'] == '1E-3'
    assert inst.parameters['PARAM3'] == '0.1F'
    assert inst.parameters['PARAM4'] == 'HELLO'
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10', 'NET12', garbage='')
    inst = subckt('X1', 'NET10', 'NET12', param1=2, param3=1e-16)
    assert inst.parameters['PARAM1'] == '2'
    assert inst.parameters['PARAM3'] == '1E-16'
