import pytest

from align.schema.library import Library
from align.schema.model import Model
from align.schema.subcircuit import Circuit
from align.schema.instance import Instance
from align.schema.types import set_context
from align.schema import types

@pytest.fixture
def library():
    return Library(loadbuiltins=True)

@pytest.fixture
def test_ckt(library):
    with set_context(library):
        mock = Circuit()
    return mock

def test_library_registration(library):
    with set_context(library):
        test = Model(
            name='TEST', prefix = 'M',
            pins=['D', 'G', 'S', 'B'],
            parameters={'W': 0, 'L': 0, 'NFIN': 1})
    library.append(test)
    assert any(x.name == types.String('TEST') for x in library)
    assert test.parent == library
    assert test.name == types.String('TEST')

def test_NMOS(library, test_ckt):
    assert any(x.name == types.String('NMOS') for x in library)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(
                name='M1',
                model='NMOS',
                pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13'},
                generator='MOS')
        with pytest.raises(Exception):
            inst = Instance(
                name='X1',
                model='NMOS',
                pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
                generator='MOS')
        inst = Instance(
            name='M1',
            model='NMOS',
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            generator='MOS')
    assert inst.name == types.String('M1')
    assert inst.model == types.String('NMOS')
    assert inst.pins == types.Dict[types.String, types.String]({
        'D': 'NET10',
        'G': 'NET12',
        'S': 'NET13',
        'B': 'VSS'
    })
    assert inst.parameters == types.Dict[types.String, types.String]({
        'W': '0',
        'L': '0',
        'NFIN': '1'
    })
    with set_context(test_ckt.elements):
        inst = Instance(
            name='M1',
            model='NMOS',
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            parameters={'NFIN': 2},
            generator='MOS')
    assert inst.parameters == types.Dict[types.String, types.String]({
        'W': '0', 
        'L': '0',
        'NFIN': '2'
    })

def test_PMOS(library, test_ckt):
    assert any(x.name == types.String('PMOS') for x in library)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(
                name='M1',
                model='PMOS',
                pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13'},
                generator='MOS')
        with pytest.raises(Exception):
            inst = Instance(
                name='X1',
                model='PMOS',
                pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
                generator='MOS')
        inst = Instance(
            name='M1',
            model='PMOS',
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            generator='MOS')
    assert inst.name == types.String('M1')
    assert inst.model == types.String('PMOS')
    assert inst.pins == types.Dict[types.String, types.String]({
        'D': 'NET10',
        'G': 'NET12',
        'S': 'NET13',
        'B': 'VSS'
    })
    assert inst.parameters == types.Dict[types.String, types.String]({
        'W': '0', 
        'L': '0',
        'NFIN': '1'
    })
    with set_context(test_ckt.elements):
        inst = Instance(
            name='M1',
            model='PMOS',
            pins={'D': 'NET10', 'G': 'NET12', 'S': 'NET13', 'B': 'VSS'},
            parameters={'NFIN': 2},
            generator='MOS')
    assert inst.parameters == types.Dict[types.String, types.String]({
        'W': '0', 
        'L': '0',
        'NFIN': '2'
    })

def test_res(library, test_ckt):
    assert any(x.name == types.String('RES') for x in library)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(name='R1', model='RES', pins={'PLUS': 'NET10'},generator='MOS')
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='RES', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
        inst = Instance(name='R1', model='RES', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
    assert inst.name == types.String('R1')
    assert inst.model == types.String('RES')
    assert inst.pins == types.Dict[types.String, types.String]({
        'PLUS': 'NET10', 
        'MINUS': 'NET12'
    })
    assert inst.parameters == types.Dict[types.String, types.String]({'VALUE': '1.3'})

def test_cap(library, test_ckt):
    assert any(x.name == types.String('CAP') for x in library)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(name='C1', model='CAP', pins={'PLUS': 'NET10'},generator='MOS')
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='CAP', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
        inst = Instance(name='C1', model='CAP', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
    assert inst.name == types.String('C1')
    assert inst.model == types.String('CAP')
    assert inst.pins == types.Dict[types.String, types.String]({
        'PLUS': 'NET10',
        'MINUS': 'NET12'
    })
    assert inst.parameters == types.Dict[types.String, types.String]({
        'VALUE': '1.3'
    })

def test_ind(library, test_ckt):
    assert any(x.name == types.String('IND') for x in library)
    with set_context(test_ckt.elements):
        with pytest.raises(Exception):
            inst = Instance(name='L1', model='IND', pins={'PLUS': 'NET10'},generator='MOS')
        with pytest.raises(Exception):
            inst = Instance(name='X1', model='IND', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
        inst = Instance(name='L1', model='IND', pins={'PLUS': 'NET10', 'MINUS':'NET12'}, parameters={'VALUE': '1.3'},generator='MOS')
    assert inst.name == types.String('L1')
    assert inst.model == types.String('IND')
    assert inst.pins == types.Dict[types.String, types.String]({
        'PLUS': 'NET10',
        'MINUS': 'NET12'
    })
    assert inst.parameters == types.Dict[types.String, types.String]({'VALUE': '1.3'})

