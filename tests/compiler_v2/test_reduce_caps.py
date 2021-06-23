import pathlib
import pytest
import pathlib
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context
from align.compiler.preprocess import add_parallel_devices, add_series_devices
@pytest.fixture
def db():
    library = Library()
    with set_context(library):
        cmodel = Model(
            name = 'CAP',
            pins = ['+', '-'],
            parameters = {
                'VALUE': '5.0'
            })
        rmodel = Model(
            name = 'RES',
            pins = ['+', '-'],
            parameters = {
                'VALUE': '5.0'
            })
        library.append(cmodel)
        library.append(rmodel)
        model_nmos = Model(
            name = 'TESTMOS',
            pins = ['D', 'G', 'S', 'B'],
            parameters = {
                'PARAM1': '1.0',
                'M':1,
                'PARAM2': '2'
            })
        library.append(model_nmos)
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['+', '-','D','G','S','B'],
            parameters = None)
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='C1', model='CAP', pins={'+': '+', '-': '-'}, parameters ={'VALUE':'2'}))
        subckt.elements.append(Instance(name='C2', model='CAP', pins={'+': '+', '-': '-'}, parameters ={'VALUE':'2'}))
        subckt.elements.append(Instance(name='R1', model='RES', pins={'+': '+', '-': '-'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='R2', model='RES', pins={'+': '+', '-': '-'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='R3', model='RES', pins={'+': '+', '-': '-'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='M1', model='TESTMOS', pins={'D': 'D', 'G': 'G', 'S': 'S', 'B': 'B'}))
        subckt.elements.append(Instance(name='M2', model='TESTMOS', pins={'D': 'D', 'G': 'G', 'S': 'S', 'B': 'B'}))

    return subckt

def test_parallel(db):

    assert db.get_element('C1').name =='C1'
    add_parallel_devices(db,update=True)
    assert db.get_element('C1').parameters == {'VALUE':'2', 'PARALLEL':2}
    assert db.get_element('R1').parameters == {'VALUE':'10', 'PARALLEL':3}
    assert db.get_element('M1').parameters == {'PARAM1':'1.0', 'M':'1', 'PARAM2':'2', 'PARALLEL':2}


@pytest.fixture
def dbs():
    library = Library()
    with set_context(library):
        cmodel = Model(
            name = 'CAP',
            pins = ['+', '-'],
            parameters = {
                'VALUE': '5.0'
            })
        rmodel = Model(
            name = 'RES',
            pins = ['+', '-'],
            parameters = {
                'VALUE': '5.0'
            })
        library.append(cmodel)
        library.append(rmodel)
        model_nmos = Model(
            name = 'TESTMOS',
            pins = ['D', 'G', 'S', 'B'],
            parameters = {
                'PARAM1': '1.0',
                'M':1,
                'PARAM2': '2'
            })
        library.append(model_nmos)
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['+', '-','D','G','S','B'],
            parameters = None)
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='C1', model='CAP', pins={'+': '+', '-': 'netc1'}, parameters ={'VALUE':'2'}))
        subckt.elements.append(Instance(name='C2', model='CAP', pins={'+': 'netc1', '-': '-'}, parameters ={'VALUE':'2'}))
        subckt.elements.append(Instance(name='R1', model='RES', pins={'+': '+', '-': 'netr1'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='R2', model='RES', pins={'+': 'netr1', '-': 'netr2'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='R3', model='RES', pins={'+': 'netr2', '-': '-'}, parameters ={'VALUE':'10'}))
        subckt.elements.append(Instance(name='M1', model='TESTMOS', pins={'D': 'D', 'G': 'G', 'S': 'netm1', 'B': 'B'}))
        subckt.elements.append(Instance(name='M2', model='TESTMOS', pins={'D': 'netm1', 'G': 'G', 'S': 'S', 'B': 'B'}))
        subckt.elements.append(Instance(name='M3', model='TESTMOS', pins={'D': 'D', 'G': 'G1', 'S': 'netm2', 'B': 'B'}))
        subckt.elements.append(Instance(name='M4', model='TESTMOS', pins={'D': 'netm2', 'G': 'G1', 'S': 'netm3', 'B': 'B'}))
        subckt.elements.append(Instance(name='M5', model='TESTMOS', pins={'D': 'netm3', 'G': 'G1', 'S': 'S', 'B': 'B'}))

    return subckt

def test_series(dbs):

    assert dbs.get_element('C1').name =='C1'
    add_series_devices(dbs,update=True)
    assert dbs.get_element('C1').parameters == {'VALUE':'2', 'STACK':2}
    assert dbs.get_element('R1').parameters == {'VALUE':'10', 'STACK':3}
    assert dbs.get_element('M1').parameters == {'PARAM1':'1.0', 'M':'1', 'PARAM2':'2', 'STACK':2}
    assert dbs.get_element('M3').parameters == {'PARAM1':'1.0', 'M':'1', 'PARAM2':'2', 'STACK':3}
    assert len(dbs.elements) ==4

