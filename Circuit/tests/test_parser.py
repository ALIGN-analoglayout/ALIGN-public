import pytest

from circuit.parser import SpiceParser

@pytest.fixture
def setup1():
    return 'X1 a b c x=1f y=0.1'

@pytest.fixture
def setup2():
    return '''
    X1 a b  c x =1f y= 0.1
    X2 a  b c x = 1f
    '''

@pytest.fixture
def parser():
    return SpiceParser()

def test_lexer_basic(setup1):
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM']
    assert len(list(SpiceParser._generate_tokens(setup1))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(setup1), types))

def test_lexer_with_comments(setup1):
    str_ = '''
X1 a b c; COMMENT ABOUT M1 pins
; SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y=0.1; AND A FW MORE FOR GOOD MEASURE
'''
    tokens = list(SpiceParser._generate_tokens(str_))
    assert tokens.pop().type == 'NEWL'
    assert all(tok1.type == tok2.type and tok1.value == tok2.value for tok1, tok2 in zip(tokens, SpiceParser._generate_tokens(setup1)))

def test_lexer_multiline(setup2):
    str_ = setup2
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NEWL']
    assert len(list(SpiceParser._generate_tokens(str_))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(str_), types))

def test_parser_basic(setup1, parser):
    parser.parse(setup1)