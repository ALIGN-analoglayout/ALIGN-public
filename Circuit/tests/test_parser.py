import pytest

from circuit.parser import SpiceParser

def test_lexer_basic():
    str_ = 'X1 a b c x=1f y=0.1'
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM']
    assert len(list(SpiceParser._generate_tokens(str_))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(str_), types))

def test_lexer_with_comments():
    str_ = '''
X1 a b c; COMMENT ABOUT M1 pins
; SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y = 0.1; AND A FW MORE FOR GOOD MEASURE
'''
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM', 'NEWL']
    assert len(list(SpiceParser._generate_tokens(str_))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(str_), types))

def test_lexer_multiline():
    str_ = '''
    X1 a b c x=1f y=0.1
    X2 a b c x=1f
    '''
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NEWL']
    assert len(list(SpiceParser._generate_tokens(str_))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(str_), types))
