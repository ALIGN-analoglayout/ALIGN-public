import pytest
import pathlib

from align.schema.subcircuit import SubCircuit
from align.schema.parser import SpiceParser

# WARNING: Parser capitalizes everything internally as SPICE is case-insensitive
#          Please formulate tests accordingly

@pytest.fixture
def setup_basic():
    return 'X1 a b testdev x=1f y=0.1'

@pytest.fixture
def setup_multiline():
    return '''
    X1 a b  testdev x =1f y= 0.1 
    X2 a  b testdev x = {capval*2}
    '''

@pytest.fixture
def setup_realistic():
    return '''
R1 vcc outplus 1e4
R2 vcc outminus 1e4

M1 outplus inplus src 0 NMOS   l=0.014u nfin=2
M2 outminus inminus src 0 NMOS l=0.014u nfin=2

C1 outplus 0 1e-12
C2 outminus 0 1e-12
'''

@pytest.fixture
def setup_annotation():
    return '''
.subckt diffamp vcc outplus outminus inplus src 0 inminus
* This is one awesome diffamp

* Subcircuit constraints can be directly specified here
* @: Order(instances=['R2', 'M1'], direction='left_to_right')
* @: Order(instances=['M1', 'M2'], direction='left_to_right')

R1 vcc outplus 1e4;  Or even here! Amazing !
R2 vcc outminus 1e4; @: Order(instances=['R1', 'R2'], direction='left_to_right')
M1 outplus inplus src 0 NMOS   l=0.014u nfin=2
M2 outminus inminus src 0 NMOS l=0.014u nfin=2

.ends
'''
@pytest.fixture
def parser():
    parser = SpiceParser()
    return parser

def test_lexer_basic(setup_basic):
    str_ = setup_basic
    types = ['NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER']
    assert [tok.type for tok in SpiceParser._generate_tokens(str_)] == types

def test_lexer_with_comments1(setup_basic):
    str_ = '''* Some comment here
X1 a b testdev; COMMENT ABOUT M1 pins
; SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y=0.1; AND A FW MORE FOR GOOD MEASURE
'''
    tokens = list(SpiceParser._generate_tokens(str_))
    assert tokens.pop(0).type == 'NEWL'
    assert all(tok1.type == tok2.type and tok1.value == tok2.value for tok1, tok2 in zip(tokens, SpiceParser._generate_tokens(setup_basic))), tokens

def test_lexer_with_comments2(setup_basic):
    str_ = '''; Some comment here
X1 a b testdev; COMMENT ABOUT M1 pins
* SOME MORE COMMENTS ABOUT PARAMETERS
+ x=1f y=0.1; AND A FW MORE FOR GOOD MEASURE
'''
    tokens = list(SpiceParser._generate_tokens(str_))
    assert tokens.pop(0).type == 'NEWL'
    assert all(tok1.type == tok2.type and tok1.value == tok2.value for tok1, tok2 in zip(tokens, SpiceParser._generate_tokens(setup_basic))), tokens

def test_lexer_multiline(setup_multiline):
    str_ = setup_multiline
    types = ['NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'EQUALS', 'EXPR', 'NEWL']
    assert [tok.type for tok in SpiceParser._generate_tokens(str_)] == types

def test_lexer_annotation(setup_annotation):
    str_ = setup_annotation
    types = ['NEWL', 'DECL', 'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'NAME', 'NUMBER', 'NAME',
             'ANNOTATION', 'ANNOTATION', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NUMBER', 'ANNOTATION', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NUMBER', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NUMBER', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER', 'NEWL',
             'DECL', 'NEWL']
    assert [tok.type for tok in SpiceParser._generate_tokens(str_)] == types

def test_lexer_realistic(setup_realistic):
    str_ = setup_realistic
    types = ['NEWL',
             'NAME', 'NAME', 'NAME', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NUMBER', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NAME', 'NAME', 'NUMBER', 'NAME', 'NAME', 'EQUALS', 'NUMBER', 'NAME', 'EQUALS', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NUMBER', 'NUMBER', 'NEWL',
             'NAME', 'NAME', 'NUMBER', 'NUMBER', 'NEWL']
    assert [tok.type for tok in SpiceParser._generate_tokens(str_)] == types

def test_parser_basic(setup_basic, parser):
    parser.library['TESTDEV'] = SubCircuit(name='TESTDEV', pins=['+', '-'], parameters={'X':'1F', 'Y':'0.1'})
    parser.parse(setup_basic)
    assert len(parser.circuit.elements) == 1
    assert parser.circuit.elements[0].name == 'X1'
    assert parser.circuit.elements[0].model.name == 'TESTDEV'
    assert parser.circuit.nets == ['A', 'B']

def test_parser_multiline(setup_multiline, parser):
    parser.library['TESTDEV'] = SubCircuit(name='TESTDEV', pins=['+', '-'], parameters={'X':'1F', 'Y':'0.1'})
    parser.parse(setup_multiline)
    assert len(parser.circuit.elements) == 2
    assert parser.circuit.elements[0].name == 'X1'
    assert parser.circuit.elements[1].name == 'X2'
    assert parser.circuit.elements[0].model.name == 'TESTDEV'
    assert parser.circuit.elements[1].model.name == 'TESTDEV'
    assert parser.circuit.nets == ['A', 'B']

def test_parser_realistic(setup_realistic, parser):
    parser.parse(setup_realistic)
    assert len(parser.circuit.elements) == 6, parser.circuit.elements
    assert [x.name for x in parser.circuit.elements] == ['R1', 'R2', 'M1', 'M2', 'C1', 'C2'], parser.circuit.elements
    assert len(parser.circuit.nets) == 7, parser.circuit.nets
    assert parser.circuit.nets == ['VCC', 'OUTPLUS', 'OUTMINUS', 'INPLUS', 'SRC', '0', 'INMINUS'], parser.circuit.nets

def test_parser_annotation(setup_annotation, parser):
    parser.parse(setup_annotation)
    assert 'DIFFAMP' in parser.library
    assert len(parser.library['DIFFAMP'].elements) == 4
    assert [x.name for x in parser.library['DIFFAMP'].elements] == ['R1', 'R2', 'M1', 'M2'], parser.library['DIFFAMP'].elements
    assert len(parser.library['DIFFAMP'].nets) == 7, parser.library['DIFFAMP'].nets
    assert parser.library['DIFFAMP'].nets == ['VCC', 'OUTPLUS', 'OUTMINUS', 'INPLUS', 'SRC', '0', 'INMINUS'], parser.circuit.nets
    assert len(parser.library['DIFFAMP'].constraints) == 3

def test_subckt_decl(setup_realistic, parser):
    parser.parse(f'''
.subckt diffamp vcc outplus outminus inplus src 0 inminus
.param res = 100
{setup_realistic}
.ends
X1 vcc outplus outminus inplus src 0 inminus diffamp res=200
''')
    assert 'DIFFAMP' in parser.library
    assert len(parser.library['DIFFAMP'].elements) == 6
    assert len(parser.circuit.elements) == 1
    assert parser.circuit.elements[0].model.name == 'DIFFAMP'

def test_model(parser):
    parser.parse('.MODEL nmos_rvt nmos KP=0.5M VT0=2')
    assert 'NMOS_RVT' in parser.library
    assert list(parser.library['NMOS_RVT'].parameters.keys()) == ['W', 'L', 'NFIN', 'KP', 'VT0']

def test_ota_cir_parsing(parser):
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'ota.cir').resolve()) as fp:
        parser.parse(fp.read())
    assert 'OTA' in parser.library
    assert len(parser.library['OTA'].elements) == 10

def test_ota_sp_parsing(parser):
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'ota.sp').resolve()) as fp:
        parser.parse(fp.read())
    assert 'OTA' in parser.library
    assert len(parser.library['OTA'].elements) == 10

def test_basic_template_parsing(parser):
    libsize = len(parser.library)
    with open((pathlib.Path(__file__).parent.parent / 'files' / 'basic_template.sp').resolve()) as fp:
        parser.parse(fp.read())
    assert len(parser.library) - libsize == 31
