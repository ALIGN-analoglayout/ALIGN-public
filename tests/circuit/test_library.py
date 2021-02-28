import pytest

from align.circuit.library import Library
from align.circuit import device

@pytest.fixture
def library():
    return Library()

def test_library_methods(library):
    assert issubclass(library.Model, device.Model)

def test_library_registration(library):
    Model = library.Model
    Model(
        name='TEST', prefix = 'M',
        pins=['D', 'G', 'S', 'B'],
        parameters={'W': 0, 'L': 0, 'NFIN': 1})
    assert 'TEST' in library
    assert library['TEST'].name == 'TEST'
