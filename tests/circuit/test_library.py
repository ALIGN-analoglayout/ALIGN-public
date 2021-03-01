import pytest

from align.circuit.library import Library
from align.circuit import device

@pytest.fixture
def library():
    return Library()

def test_library_registration(library):
    device.Model(
        name='TEST', prefix = 'M',
        pins=['D', 'G', 'S', 'B'],
        parameters={'W': 0, 'L': 0, 'NFIN': 1},
        library=library)
    assert 'TEST' in library
    assert library['TEST'].name == 'TEST'
