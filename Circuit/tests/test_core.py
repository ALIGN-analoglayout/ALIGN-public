import pytest

from circuit.core import *

def test_n_terminal_device():
    inst = NTerminalDevice('X1')
    assert inst.name == 'X1'
    with pytest.raises(AssertionError):
        inst = NTerminalDevice('X2', 'net1')
