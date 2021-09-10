import pydantic
import pytest
from align.schema import types

from align.schema.model import Model
from align.schema.types import set_context, List


@pytest.fixture()
def library():
    return List[Model]()


@pytest.fixture()
def testmos(library):
    with set_context(library):
        model = Model(
            name='TESTMOS',
            pins=['D', 'G', 'S', 'B'],
            parameters={
                'PARAM1': '1.0',
                'PARAM2': '2'
            })
        library.append(model)
        return model


def test_new_model(library):
    with set_context(library):
        with pytest.raises(Exception):
            MyDevice = Model()
        with pytest.raises(Exception):
            MyDevice = Model(name='MyDevice')
        MyDevice = Model(
            name='MyDevice',
            pins=['D', 'S'],
            parameters={
                'PARAM1': '1.0',
                'PARAM2': '2'
            })


def test_derived_model(testmos):
    with set_context(testmos.parent):
        with pytest.raises(Exception):
            MyDevice = Model(base='TESTMOS')
        with pytest.raises(Exception):
            MyDevice = Model(name='MyDevice')
        with pytest.raises(Exception):
            MyDevice = Model(
                name='MyDevice', base='TESTMOS',
                pins=['D', 'G'], parameters={'PARAM1': '3'})
        with pytest.raises(Exception):
            MyDevice = Model(
                name='MyDevice', base='TESTMOS',
                pins=['D', 'G'], parameters={'PARAM1': '3'})
        MyDevice = Model(
            name='MyDevice', base='TESTMOS',
            parameters={'PARAM1': '3'})


def test_base_model_case_insensitivity(library):
    '''
    Everything should be converted to uppercase internally
        (SPICE is case-insensitive)
    '''
    with set_context(library):
        MyDevice = Model(
            name='MyDevice',
            pins=['d', 'S'],
            parameters={
                'PARAM1': 'nf*4',
                'param2': '2'
            })
    assert isinstance(MyDevice.name, types.String), type(MyDevice.name)
    assert MyDevice.name == types.String('MYDEVICE')
    assert MyDevice.pins == types.List[types.String](['D', 'S'])
    assert MyDevice.parameters == types.Dict[types.String, types.String]({
        'PARAM1': 'NF*4',
        'PARAM2': '2'
    })


def test_derived_model_case_insensitivity(testmos):
    with set_context(testmos.parent):
        DerivedMOS = Model(
            name='DerivedMOS',
            base='testmos',
            parameters={'param1': 'nf*4'})
    assert DerivedMOS.name == types.String('DERIVEDMOS')
    assert DerivedMOS.base == types.String('TESTMOS')
    assert DerivedMOS.pins == types.List[types.String](['D', 'G', 'S', 'B'])
    assert DerivedMOS.parameters == types.Dict[types.String, types.String]({
        'PARAM1': 'NF*4',
        'PARAM2': '2'
    })


def test_derived_model_new_parameters(testmos):
    with set_context(testmos.parent):
        DerivedMOS = Model(
            name='DERIVEDMOS',
            base='testmos',
            parameters={
                'PARAM1': 'NF*6',
                'PARAM3': 'NF*4'})
    assert DerivedMOS.parameters == types.Dict[types.String, types.String]({
        'PARAM1': 'NF*6',
        'PARAM2': '2',
        'PARAM3': 'NF*4'
    })


def test_model_str_casting(library):
    '''
    Parameter values are stored as string internally
    (for model consistency)
    '''
    with set_context(library):
        MyDevice = Model(
            name='MyDevice',
            pins=['D', 'S'],
            parameters={
                'PARAM1': 1.0,
                'PARAM2': 2
            })
    assert MyDevice.parameters == types.Dict[types.String, types.String]({
        'PARAM1': '1.0',
        'PARAM2': '2'
    })


def test_model_json(testmos):
    assert testmos.json(
    ) == '{"name": "TESTMOS", "base": null, "pins": ["D", "G", "S", "B"], "parameters": {"PARAM1": "1.0", "PARAM2": "2"}, "prefix": null}'


def test_model_xyce(testmos):
    assert testmos.xyce(
    ) == '* .MODEL TESTMOS ElementaryDevice(D, G, S, B) PARAM1={1.0} PARAM2={2}'
    with set_context(testmos.parent):
        newmos = Model(name='newmos', base='TESTMOS',
                       parameters={'param3': '3'})
    assert newmos.xyce(
    ) == '.MODEL newmos TESTMOS PARAM1={1.0} PARAM2={2} param3={3}'
