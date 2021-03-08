import pytest

from align.schema.library import Library
from align.schema import model
from align.schema.instance import Instance

@pytest.fixture
def library():
    return Library(loadbuiltins=True)

def test_library_registration(library):
    library['TEST'] = model.Model(
        name='TEST', prefix = 'M',
        pins=['D', 'G', 'S', 'B'],
        parameters={'W': 0, 'L': 0, 'NFIN': 1})
    assert 'TEST' in library
    assert library['TEST'].name == 'TEST'

def test_NMOS(library):
    assert 'NMOS' in library
    with pytest.raises(Exception):
        inst = Instance(
            name='M1',
            model=library['NMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13'})
    with pytest.raises(Exception):
        inst = Instance(
            name='X1',
            model=library['NMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'})
    inst = Instance(
            name='M1',
            model=library['NMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'})
    assert inst.name == 'M1'
    assert inst.model.name == 'NMOS'
    assert inst.pins == {'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'}
    assert list(inst.parameters.keys()) == ['W', 'L', 'NFIN']
    assert inst.parameters['W'] == '0'
    assert inst.parameters['L'] == '0'
    assert inst.parameters['NFIN'] == '1'
    inst = Instance(
            name='M1',
            model=library['NMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            parameters={'NFIN': 2})
    assert inst.parameters['NFIN'] == '2'

def test_PMOS(library):
    assert 'PMOS' in library
    with pytest.raises(Exception):
        inst = Instance(
            name='M1',
            model=library['PMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13'})
    with pytest.raises(Exception):
        inst = Instance(
            name='X1',
            model=library['PMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'})
    inst = Instance(
            name='M1',
            model=library['PMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'})
    assert inst.name == 'M1'
    assert inst.model.name == 'PMOS'
    assert inst.pins == {'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'}
    assert list(inst.parameters.keys()) == ['W', 'L', 'NFIN']
    assert inst.parameters['W'] == '0'
    assert inst.parameters['L'] == '0'
    assert inst.parameters['NFIN'] == '1'
    inst = Instance(
            name='M1',
            model=library['PMOS'],
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            parameters={'NFIN': 2})
    assert inst.parameters['NFIN'] == '2'

def test_res(library):
    assert 'RES' in library
    with pytest.raises(Exception):
        inst = Instance(name='R1', model=library['RES'], pins={'+': 'NET10'})
    with pytest.raises(Exception):
        inst = Instance(name='X1', model=library['RES'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    inst = Instance(name='R1', model=library['RES'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    assert inst.name == 'R1'
    assert inst.model.name == 'RES'
    assert inst.pins == {'+': 'NET10', '-': 'NET12'}
    assert inst.parameters['VALUE'] == '1.3'

def test_cap(library):
    assert 'CAP' in library
    with pytest.raises(Exception):
        inst = Instance(name='C1', model=library['CAP'], pins={'+': 'NET10'})
    with pytest.raises(Exception):
        inst = Instance(name='X1', model=library['CAP'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    inst = Instance(name='C1', model=library['CAP'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    assert inst.name == 'C1'
    assert inst.model.name == 'CAP'
    assert inst.pins == {'+': 'NET10', '-': 'NET12'}
    assert inst.parameters['VALUE'] == '1.3'

def test_ind(library):
    assert 'IND' in library
    with pytest.raises(Exception):
        inst = Instance(name='L1', model=library['IND'], pins={'+': 'NET10'})
    with pytest.raises(Exception):
        inst = Instance(name='X1', model=library['IND'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    inst = Instance(name='L1', model=library['IND'], pins={'+': 'NET10', '-':'NET12'}, parameters={'VALUE': '1.3'})
    assert inst.name == 'L1'
    assert inst.model.name == 'IND'
    assert inst.pins == {'+': 'NET10', '-': 'NET12'}
    assert inst.parameters['VALUE'] == '1.3'

