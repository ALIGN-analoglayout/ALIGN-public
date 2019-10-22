import pytest

from circuit.parser import SpiceParser

def test_lexer():
    assert len(list(SpiceParser._generate_tokens('M1 a b c x=1f y=0.1'))) == 10
    assert len(list(SpiceParser._generate_tokens('''
M1 a b c; COMMENT ABOUT M1 pins
; SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y = 0.1; AND A FW MORE FOR GOOD MEASURE
'''))) == 10

    assert len(list(SpiceParser._generate_tokens('''
    M1 a b c x=1f y=0.1
    M2 a b c x=1f
    '''))) == 19 # Includes 2 <NEWL>s
