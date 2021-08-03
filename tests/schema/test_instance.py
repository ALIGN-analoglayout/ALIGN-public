import pytest

from align.schema.model import Model
from align.schema.instance import Instance
from align.schema.subcircuit import Circuit
from align.schema.types import set_context, List

@pytest.fixture()
def library():
    library = List[Model]()
    with set_context(library):
        model = Model(
            name = 'TESTMOS',
            pins = ['D', 'G', 'S', 'B'],
            parameters = {
                'PARAM1': '1.0',
                'PARAM2': '2'
            })
    library.append(model)
    return library

@pytest.fixture()
def circuit(library):
    with set_context(library):
        mock_subckt = Circuit()
    return mock_subckt

def test_instance_model(circuit):
    with set_context(circuit.elements):
        with pytest.raises(Exception):
            M1 = Instance()
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                pins={'D': 'NET01', 'G': 'NET02', 'S':'NET03', 'B':'NET04'}
            )
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
                parameters={'PARAM1':'12', 'PARAM2': '13'}
            )
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                model='undefinedmos',
                pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
                parameters={'PARAM1':'12', 'PARAM2': '13'}
            )
        M1 = Instance(
            name='M1',
            model='testmos',
            pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
            parameters={'PARAM1':'12', 'PARAM2': '13'}
        )

def test_instance_name(circuit):
    with set_context(circuit.elements):
        with pytest.raises(Exception):
            M1 = Instance(model='testmos')
        with pytest.raises(Exception):
            M1 = Instance(name='M1')
        with pytest.raises(Exception):
            M1 = Instance(name='M1', model='testmos')

def test_instance_pins(circuit):
    with set_context(circuit.elements):
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                model='testmos',
                pins={'D': 'NET01'})
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                model='testmos',
                pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B':'NET04'},
                parameters={'garbage': 'NET05'}
            )
        with pytest.raises(Exception):
            M1 = Instance(
                name='M1',
                model='testmos',
                pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
                parameters={'garbage':'dfddfd'}
            )
        M1 = Instance(
            name='M1',
            model='testmos',
            pins={'D': 'NET01', 'G': 'NET02', 'S':'NET03', 'B':'NET04'}
        )
    assert M1.name == 'M1'
    assert M1.model == 'TESTMOS'
    assert M1.pins == {'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'}
    assert M1.parameters == {'PARAM1': "1.0", 'PARAM2': "2"}

def test_instance_init_parameters(circuit):
    with set_context(circuit.elements):
        M1 = Instance(
            name='M1',
            model='testmos',
            pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
            parameters={'PARAM1':'NF*4'}
        )
    assert M1.parameters == {'PARAM1': 'NF*4', 'PARAM2': "2"}
    with set_context(circuit.elements):
        M1 = Instance(
            name='M1',
            model='testmos',
            pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
            parameters={'PARAM1':'12', 'PARAM2': '13'}
        )
    assert M1.parameters == {'PARAM1': "12", 'PARAM2': "13"}

def test_model_instantiation(circuit):
    with set_context(circuit.elements):
        M1 = Instance(
                name='m1',
                model='testmos',
                pins={'d': 'net01', 'G': 'Net02', 's': 'NET03', 'B': 'NeT04'},
                parameters={'PARAM1':'nf*4', 'param2':'2.0'}
            )
        M2 =Instance(
                name='m2',
                model='testmos',
                pins={'d': 'net03', 'G': 'Net02', 's': 'NET01', 'B': 'NeT04'},
                parameters={'PARAM1':'2.0', 'param2':'nf*4'}
            )
    assert M1  != M2
    assert M1.name != M2.name
    assert M1.pins != M2.pins
    assert M1.parameters != M2.parameters
    assert M1.model == M2.model

def test_instance_case_insensitivity(circuit):
    '''
    Everything should be converted to uppercase internally
        (SPICE is case-insensitive)
    '''
    with set_context(circuit.elements):
        M1 = Instance(
            name='m1',
            model='testmos',
            pins={'d': 'net01', 'G': 'Net02', 's': 'NET03', 'B': 'NeT04'},
            parameters={'PARAM1':'nf*4', 'param2':'2.0'}
        )
    assert M1.name == 'M1'
    assert M1.pins == {'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'}
    assert M1.parameters == {'PARAM1': 'NF*4', 'PARAM2': "2.0"}

def test_instance_json(circuit):
    with set_context(circuit.elements):
        M1 = Instance(
        name='M1',
        model='testmos',
        pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
        parameters={'PARAM1':'NF*4'})
    assert M1.json() == '{"model": "TESTMOS", "name": "M1", "pins": {"D": "NET01", "G": "NET02", "S": "NET03", "B": "NET04"}, "parameters": {"PARAM1": "NF*4", "PARAM2": "2"}, "generator": null, "abstract_name": null}'
