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
        model_pmos = Model(
            name = 'PMOS',
            pins = ['D', 'G', 'S', 'B'])
        library.append(model_pmos)
        model_nmos = Model(
            name = 'NMOS',
            pins = ['D', 'G', 'S', 'B'])
        library.append(model_nmos)
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['VDD', 'G','GND','B'],
            parameters = None)
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='M1', model='PMOS', pins={'D': 'VDD', 'G': 'G', 'S': 'GND', 'B': 'B'}, generator='PMOS'))
        subckt.elements.append(Instance(name='M2', model='PMOS', pins={'D': 'NET1', 'G': 'G', 'S': 'VDD', 'B': 'B'}, generator='PMOS'))
        subckt.elements.append(Instance(name='M3', model='PMOS', pins={'D': 'NET1', 'G': 'G', 'S': 'GND', 'B': 'B'}, generator='PMOS'))
        subckt.elements.append(Instance(name='M4', model='NMOS', pins={'D': 'VDD', 'G': 'G', 'S': 'GND', 'B': 'B'}, generator='PMOS'))
        subckt.elements.append(Instance(name='M5', model='NMOS', pins={'D': 'GND', 'G': 'G', 'S': 'VDD', 'B': 'B'}, generator='PMOS'))
    return subckt

def test_swap(db):

    assert db.get_element('M1').name =='M1'
    define_SD(db,['VDD'],['GND'],digital=['SUBCKT'])
    assert db.get_element('M1').pins== {'D': 'VDD', 'G': 'G', 'S': 'GND', 'B': 'B'}
    define_SD(db,['VDD'],['GND'])
    assert db.get_element('M1').pins== {'D': 'GND', 'G': 'G', 'S': 'VDD', 'B': 'B'}
    assert db.get_element('M2').pins== {'D': 'NET1', 'G': 'G', 'S': 'VDD', 'B': 'B'}
    assert db.get_element('M3').pins== {'D': 'GND', 'G': 'G', 'S': 'NET1', 'B': 'B'}
    assert db.get_element('M4').pins== {'D': 'VDD', 'G': 'G', 'S': 'GND', 'B': 'B'}
    assert db.get_element('M5').pins== {'D': 'VDD', 'G': 'G', 'S': 'GND', 'B': 'B'}



