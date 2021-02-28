import pytest

from align.circuit import device

@pytest.fixture()
def testmos():
    return device.BaseModel(
        name = 'TestMOS',
        pins = ['D', 'G', 'S', 'B'],
        parameters = {
            'PARAM1': 1.0,
            'PARAM2': 2
        })

def test_new_model():
    with pytest.raises(Exception):
        MyDevice = device.BaseModel()
    with pytest.raises(Exception):
        MyDevice = device.BaseModel(name='MyDevice')
    MyDevice = device.BaseModel(
        name = 'MyDevice',
        pins = ['D', 'S'],
        parameters = {
            'PARAM1': 1.0,
            'PARAM2': 2
        })

def test_derived_model(testmos):
    with pytest.raises(Exception):
        MyDevice = device.Model(base=testmos)
    with pytest.raises(Exception):
        MyDevice = device.Model(name='MyDevice')
    with pytest.raises(Exception):
        MyDevice = device.Model(
            name='MyDevice', base=testmos,
            pins=['D', 'G'], parameters={'PARAM1': 3})
    with pytest.raises(Exception):
        MyDevice = device.Model(
            name='MyDevice', base=testmos,
            pins=['D', 'G'], parameters={'PARAM1': 3})
    MyDevice = device.Model(
        name='MyDevice', base=testmos,
        parameters={'PARAM1': 3})

def test_model_instance(testmos):
    with pytest.raises(Exception):
        M1 = testmos()
    with pytest.raises(Exception):
        M1 = testmos('M1')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'net01')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04', 'net05')
    M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04')
    with pytest.raises(Exception):
        M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04', garbage='dfddfd')
    M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04', PARAM1='nf*4')
    M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04', PARAM1=12)
    M1 = testmos('M1', 'net01', 'net02', 'net03', 'net04', PARAM2=13)

# def test_model(ThreeTerminalDevice):
#     CustomDevice = BaseModel('CustomDevice', ThreeTerminalDevice, newparam=1, newparam2='hello')
#     with pytest.raises(AssertionError):
#         inst = CustomDevice('X1', 'net01', 'net02', 'net03', garbage=2)
#     inst = CustomDevice('X1', 'net01', 'net02', 'net03', myparameter=2, newparam=2)
#     assert type(inst).__name__ == 'CustomDevice'
#     assert inst.pins == {'a': 'net01', 'b': 'net02', 'c': 'net03'}
#     assert inst.parameters == {'myparameter': 2, 'newparam': 2, 'newparam2': 'hello'}
