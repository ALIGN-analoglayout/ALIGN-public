from align.circuit.subcircuit import SubCircuit

def TEST_SUBCKT():
    subckt = core.SubCircuit(
        name = 'TEST_SUBCKT',
        pins = ['pin1', 'pin2'],
        parameters = {'param1':1, 'param2':'1e-3', 'param3':'0.1f', 'param4':'hello'})
    with pytest.raises(Exception):
        inst = subckt('X1')
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10')
    inst = subckt('X1', 'NET10', 'NET12')
    assert inst.name == 'X1'
    assert inst.model.name == 'TEST_SUBCKT'
    assert inst.pins == {'pin1': 'NET10', 'pin2': 'NET12'}
    assert list(inst.parameters.keys()) == ['param1', 'param2', 'param3', 'param4']
    assert inst.parameters['param1'] == '1'
    assert inst.parameters['param2'] == '1e-3'
    assert inst.parameters['param3'] == '1e-16'
    assert inst.parameters['param4'] == 'hello'
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10', 'NET12', garbage='')
    with pytest.raises(Exception):
        inst = subckt('X1', 'NET10', 'NET12', param1='invalid_number')
    inst = subckt('X1', 'NET10', 'NET12', param1=2, param3=1e-16)
    assert inst.parameters['param1'] == '2'
    assert inst.parameters['param3'] == '1e-16'
