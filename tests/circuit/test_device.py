import pytest

from align.circuit import device

@pytest.fixture()
def testmos():
    return device.Model(
        name = 'TESTMOS',
        pins = ['D', 'G', 'S', 'B'],
        parameters = {
            'PARAM1': '1.0',
            'PARAM2': '2'
        })

def test_new_model():
    with pytest.raises(Exception):
        MyDevice = device.Model()
    with pytest.raises(Exception):
        MyDevice = device.Model(name='MyDevice')
    MyDevice = device.Model(
        name = 'MyDevice',
        pins = ['D', 'S'],
        parameters = {
            'PARAM1': '1.0',
            'PARAM2': '2'
        })

def test_derived_model(testmos):
    with pytest.raises(Exception):
        MyDevice = device.Model(base='TESTMOS')
    with pytest.raises(Exception):
        MyDevice = device.Model(name='MyDevice')
    with pytest.raises(Exception):
        MyDevice = device.Model(
            name='MyDevice', base='TESTMOS',
            pins=['D', 'G'], parameters={'PARAM1': '3'})
    with pytest.raises(Exception):
        MyDevice = device.Model(
            name='MyDevice', base='TESTMOS',
            pins=['D', 'G'], parameters={'PARAM1': '3'})
    MyDevice = device.Model(
        name='MyDevice', base='TESTMOS',
        parameters={'PARAM1': '3'})

def test_base_model_case_insensitivity():
    '''
    Everything should be converted to uppercase internally
        (SPICE is case-insensitive)
    '''
    MyDevice = device.Model(
        name = 'MyDevice',
        pins = ['d', 'S'],
        parameters = {
            'PARAM1': 'nf*4',
            'param2': '2'
        })
    assert MyDevice.name == 'MYDEVICE'
    assert MyDevice.pins == ['D', 'S']
    assert MyDevice.parameters == {
        'PARAM1': 'NF*4',
        'PARAM2': '2'
    }

def test_derived_model_case_insensitivity(testmos):
    DerivedMOS = device.Model(
        name = 'DerivedMOS',
        base = 'TestMOS',
        parameters = {'param1': 'nf*4'})
    assert DerivedMOS.name == 'DERIVEDMOS'
    assert DerivedMOS.base == 'TESTMOS'
    assert DerivedMOS.pins == ['D', 'G', 'S', 'B']
    assert DerivedMOS.parameters == {'PARAM1': 'NF*4', 'PARAM2': '2'}

def test_derived_model_new_parameters(testmos):
    DerivedMOS = device.Model(
        name = 'DERIVEDMOS',
        base = 'TESTMOS',
        parameters = {
            'PARAM1': 'NF*6',
            'PARAM3': 'NF*4'})
    assert DerivedMOS.parameters == {
            'PARAM1': 'NF*6',
            'PARAM2': '2',
            'PARAM3': 'NF*4'
    }
def test_model_str_casting():
    '''
    Parameter values are stored as string internally
    (for model consistency)
    '''
    MyDevice = device.Model(
        name = 'MyDevice',
        pins = ['D', 'S'],
        parameters = {
            'PARAM1': 1.0,
            'PARAM2': 2
        })
    assert MyDevice.parameters == {
        'PARAM1': '1.0',
        'PARAM2': '2'
    }

def test_instance_init(testmos):
    with pytest.raises(Exception):
        M1 = testmos()
    with pytest.raises(Exception):
        M1 = testmos('M1')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'NET01')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', 'NET05')
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', garbage='dfddfd')
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04')
    assert M1.name == 'M1'
    assert M1.model.name == 'TESTMOS'
    assert M1.pins == {'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'}
    assert M1.parameters == {'PARAM1': "1.0", 'PARAM2': "2"}
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', PARAM1='NF*4')
    assert M1.parameters == {'PARAM1': 'NF*4', 'PARAM2': "2"}
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', PARAM1='12', PARAM2='13')
    assert M1.parameters == {'PARAM1': "12", 'PARAM2': "13"}

def test_instance_case_insensitivity(testmos):
    '''
    Everything should be converted to uppercase internally
        (SPICE is case-insensitive)
    '''
    M1 = testmos('m1', 'net01', 'Net02', 'NET03', 'NeT04', PARAM1='nf*4', param2='2.0')
    assert M1.name == 'M1'
    assert M1.pins == {'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'}
    assert M1.parameters == {'PARAM1': 'NF*4', 'PARAM2': "2.0"}

def test_model_json(testmos):
    assert testmos.json() == '{"name": "TESTMOS", "base": null, "pins": ["D", "G", "S", "B"], "parameters": {"PARAM1": "1.0", "PARAM2": "2"}, "prefix": null}'

def test_instance_json(testmos):
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', PARAM1='NF*4')
    assert M1.json() == '{"model": {"name": "TESTMOS"}, "name": "M1", "pins": {"D": "NET01", "G": "NET02", "S": "NET03", "B": "NET04"}, "parameters": {"PARAM1": "NF*4", "PARAM2": "2"}}'
