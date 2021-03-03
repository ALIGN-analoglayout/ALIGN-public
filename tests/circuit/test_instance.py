import pytest

from align.circuit.model import Model
from align.circuit.instance import Instance

@pytest.fixture()
def testmos():
    return Model(
        name = 'TESTMOS',
        pins = ['D', 'G', 'S', 'B'],
        parameters = {
            'PARAM1': '1.0',
            'PARAM2': '2'
        })

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

def test_instance_json(testmos):
    M1 = testmos('M1', 'NET01', 'NET02', 'NET03', 'NET04', PARAM1='NF*4')
    assert M1.json() == '{"model": {"name": "TESTMOS"}, "name": "M1", "pins": {"D": "NET01", "G": "NET02", "S": "NET03", "B": "NET04"}, "parameters": {"PARAM1": "NF*4", "PARAM2": "2"}}'
