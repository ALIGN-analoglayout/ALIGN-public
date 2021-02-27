import pytest

from align.circuit.library import Library

@pytest.fixture
def library():
    return Library()

def test_NMOS(library):
    assert 'NMOS' in library
    assert library['NMOS'].__name__ == 'NMOS'

def test_PMOS(library):
    assert 'PMOS' in library
    assert library['PMOS'].__name__ == 'PMOS'

def test_res(library):
    assert 'RES' in library
    assert library['RES'].__name__ == 'RES'

def test_cap(library):
    assert 'CAP' in library
    assert library['CAP'].__name__ == 'CAP'
