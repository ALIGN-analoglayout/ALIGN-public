import pytest

from circuit.elements import SubCircuit
from circuit.parser import SpiceParser

@pytest.fixture
def setup_basic():
    return 'X1 a b testdev x=1f y=0.1'

@pytest.fixture
def setup_multiline():
    return '''
    X1 a b  testdev x =1f y= 0.1
    X2 a  b testdev x = 1f
    '''
@pytest.fixture
def parser():
    parser = SpiceParser()
    parser.library['testdev'] = SubCircuit('testdev', 'pin1', 'pin2', x='1f', y=0.1)
    return parser

def test_lexer_basic(setup_basic):
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM']
    assert len(list(SpiceParser._generate_tokens(setup_basic))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(setup_basic), types))

def test_lexer_with_comments(setup_basic):
    str_ = '''
X1 a b testdev; COMMENT ABOUT M1 pins
; SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y=0.1; AND A FW MORE FOR GOOD MEASURE
'''
    tokens = list(SpiceParser._generate_tokens(str_))
    assert tokens.pop().type == 'NEWL'
    assert all(tok1.type == tok2.type and tok1.value == tok2.value for tok1, tok2 in zip(tokens, SpiceParser._generate_tokens(setup_basic)))

def test_lexer_multiline(setup_multiline):
    str_ = setup_multiline
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NAME', 'EQUALS', 'NUM', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUM', 'NEWL']
    assert len(list(SpiceParser._generate_tokens(str_))) == len(types)
    assert all(tok.type == type_ for tok, type_ in zip(SpiceParser._generate_tokens(str_), types))

def test_parser_basic(setup_basic, parser):
    parser.parse(setup_basic)
    assert len(parser.circuit.elements) == 1
    assert parser.circuit.elements[0].name == 'X1'
    assert isinstance(parser.circuit.elements[0], parser.library['testdev'])
    assert parser.circuit.nets == ['a', 'b']

def test_parser_multiline(setup_multiline, parser):
    parser.parse(setup_multiline)
    assert len(parser.circuit.elements) == 2
    assert parser.circuit.elements[0].name == 'X1'
    assert parser.circuit.elements[1].name == 'X2'
    assert isinstance(parser.circuit.elements[0], parser.library['testdev'])
    assert isinstance(parser.circuit.elements[1], parser.library['testdev'])
    assert parser.circuit.nets == ['a', 'b']