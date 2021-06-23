import pathlib
import pytest
import pathlib
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context
from align.compiler.preprocess import define_SD
@pytest.fixture
def db():
    library = Library()
    with set_context(library):
        model = Model(
            name = 'TESTMOS',
            pins = ['D', 'G', 'S', 'B'],
            parameters = {
                'PARAM1': '1.0',
                'M':1,
                'PARAM2': '2'
            })
        library.append(model)
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['D', 'G','S','B'],
            parameters = None)
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='M1', model='TESTMOS', pins={'D': 'D', 'G': 'G', 'S': 'S1', 'B': 'B'}))
        subckt.elements.append(Instance(name='M2', model='TESTMOS', pins={'D': 'S1', 'G': 'G', 'S': 'S2', 'B': 'B'}))
        subckt.elements.append(Instance(name='M3', model='TESTMOS', pins={'D': 'S2', 'G': 'G', 'S': 'S3', 'B': 'B'}))
        subckt.elements.append(Instance(name='M4', model='TESTMOS', pins={'D': 'S3', 'G': 'G', 'S': 'S4', 'B': 'B'}))
        subckt.elements.append(Instance(name='M5', model='TESTMOS', pins={'D': 'S4', 'G': 'G', 'S': 'S5', 'B': 'B'}))
        subckt.elements.append(Instance(name='M6', model='TESTMOS', pins={'D': 'S5', 'G': 'G', 'S': 'S', 'B': 'B'}))
    return subckt

def test_Stack(db):

    assert db.get_element('M1') =='M1'
