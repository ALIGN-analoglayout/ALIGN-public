# example.py
#
# An example of writing a simple recursive descent parser

import re
import collections

# Token specification
SEMI = r'(?P<SEMI>;)'
LPAREN = r'(?P<LPAREN>\()'
RPAREN = r'(?P<RPAREN>\))'
MINUS = r'(?P<MINUS>\-)'
PLUS = r'(?P<PLUS>\+)'
NAME = r'(?P<NAME>[a-zA-Z_][a-zA-Z_0-9]*)'
NUM =  r'(?P<NUM>[-+]?\d*\.\d+|\d+\.?)'
LIT =  r'(?P<LIT>\".*\")'
WS     = r'(?P<WS>\s+)'

master_pat = re.compile('|'.join([SEMI,LPAREN,RPAREN,MINUS,PLUS,NAME,NUM,LIT,WS]))

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

def generate_tokens(text):
    scanner = master_pat.scanner(text)
    for m in iter(scanner.match, None):
        tok = Token(m.lastgroup, m.group())
        if tok.type != 'WS':
            yield tok

# Parser 
class DEFParser:
    '''
    Implementation of a recursive descent parser for DEF.   Each method
    implements a single grammar rule.

    Use the ._accept() method to test and accept the current lookahead token.
    Use the ._accept_keyword() method to test and accept the current
    lookahead token if it matches the argument.
    Use the ._expect() method to exactly match and discard the next token on
    the input (or raise a SyntaxError if it doesn't match).
    '''

    def parse(self,text):
        self.tokens = generate_tokens(text)
        self.tok = None             # Last symbol consumed
        self.nexttok = None         # Next symbol tokenized
        self._advance()             # Load first lookahead token
        return self.whole()

    def _advance(self):
        'Advance one token ahead'
        self.tok, self.nexttok = self.nexttok, next(self.tokens, None)
#        print( self.tok, self.nexttok)

    def _accept(self,toktype):
        'Test and consume the next token if it matches toktype'
        if self.nexttok and self.nexttok.type == toktype:
            self._advance()
            return True
        else:
            return False

    def _accept_keyword(self,str):
        'Test and consume the next token if it matches the keyword str'
        if self.nexttok and self.nexttok.type == 'NAME' and self.nexttok.value == str:
            self._advance()
            return True
        else:
            return False

    def _expect(self,toktype):
        'Consume next token if it matches toktype or raise SyntaxError'
        if not self._accept(toktype):
            raise SyntaxError('Expected ' + toktype)

    def _expect_keyword(self,str):
        'Consume next token if it matches argument or raise SyntaxError'
        if not self._accept_keyword(str):
            raise SyntaxError('Expected keyword' + str)

    # Grammar rules follow

    def point(self):
        self._expect( 'LPAREN')
        self._expect( 'NUM')
        self._expect( 'NUM')
        self._expect( 'RPAREN')

    def rect(self):
        self.point()
        self.point()

    def whole(self):

        while True:
            if self._accept_keyword('END'):
                self._accept_keyword('DESIGN')
                break
            elif self._accept_keyword( 'VERSION'): 
                self._expect('NUM')
                self._expect('SEMI')
            elif self._accept_keyword( 'BUSBITCHARS'):
                self._expect('LIT')
                self._expect('SEMI')
            elif self._accept_keyword( 'DIVIDERCHAR'):
                self._expect('LIT')
                self._expect('SEMI')
            elif self._accept_keyword( 'DESIGN'):
                self._expect('NAME')
                self._expect('SEMI')
            elif self._accept_keyword( 'UNITS'):
                self._expect('NAME')
                self._expect('NAME')
                self._expect('NUM')
                self._expect('SEMI')
            elif self._accept_keyword( 'PROPERTYDEFINITIONS'):
                while True:
                    if self._accept_keyword('END'):
                        self._accept_keyword('PROPERTYDEFINITIONS')
                        break
                    elif self._accept_keyword( 'DESIGN'):
                        self._expect('NAME')
                        if self._accept_keyword( 'STRING'):
                            self._expect( 'LIT')
                        elif self._accept_keyword( 'INTEGER'):
                            self._expect('NUM')
                        else:
                            raise SyntaxError('Expected STRING or INTEGER keywords')
                        self._expect('SEMI')
                    else:
                        raise SyntaxError('Expected END or MACRO keywords')
            elif self._accept_keyword( 'DIEAREA'):
                self.rect()
                self._expect( 'SEMI')

            elif self._accept_keyword( 'PINS'):
                self._expect('NUM')
                pinCount = int(self.tok.value)
                self._expect('SEMI')

                pins = []
                while True:
                    if self._accept_keyword( 'END'):
                        assert len(pins) == pinCount
                        self._expect_keyword('PINS')
                        break
                    elif self._accept( 'MINUS'):
                        self._expect('NAME')
                        pins.append( self.tok.value)
                        self._expect('PLUS')
                        self._expect_keyword( 'NET')
                        self._expect('NAME')
                        while self._accept( 'PLUS'):
                            if self._accept_keyword( 'DIRECTION'):
                                self._expect('NAME')    
                            elif self._accept_keyword( 'PORT'):
                                while self._accept( 'PLUS'):
                                    if self._accept_keyword( 'LAYER'):
                                        self._expect('NAME')    
                                        self.rect()
                                    elif self._accept_keyword( 'PLACED'):
                                        self.point()
                                        self._expect( 'NAME')
                                        self._expect( 'SEMI')
                                    else:
                                        raise SyntaxError('Expected LAYER or PLACED keywords.')     
            elif self._accept_keyword( 'BLOCKAGES'):
                self._expect('NUM')
                blockageCount = int(self.tok.value)
                self._expect('SEMI')
                blockages = []

                while True:
                    if self._accept_keyword( 'END'):
                        assert len(blockages) == blockageCount
                        self._expect_keyword('BLOCKAGES')
                        break
                    elif self._accept( 'MINUS'):
                        self._expect_keyword('LAYER')
                        self._expect( 'NAME')
                        blockages.append( self.tok.value)
                        self._expect_keyword( 'RECT')
                        self.rect()
                        self._expect( 'SEMI')
            elif self._accept_keyword( 'NETS'):
                self._expect('NUM')
                netCount = int(self.tok.value)
                self._expect('SEMI')

                nets = []
                while True:
                    if self._accept_keyword( 'END'):
                        assert len(nets) == netCount
                        self._expect_keyword('NETS')
                        break
                    elif self._accept( 'MINUS'):
                        self._expect('NAME')
                        nets.append( self.tok.value)
                        self._expect( 'LPAREN')
                        self._expect_keyword( 'PIN')
                        self._expect('NAME')
                        self._expect( 'RPAREN')
                        self._expect( 'SEMI')
            else:                        
                raise SyntaxError( 'Expected PROPERTYDEFINITIONS, DIEAREA, PINS, BLOCKAGES or NETS keywords')

def test_def():
    str = """VERSION 5.7 ;
DIVIDERCHAR "/" ;
BUSBITCHARS "[]" ;

DESIGN current_mirror_nmos ;

UNITS DISTANCE MICRONS 4000 ;
PROPERTYDEFINITIONS
  DESIGN function STRING "transistor" ;
  DESIGN _pcCompiledCounter INTEGER 846 ;
  DESIGN viewSubType STRING "maskLayoutParamCell" ;
END PROPERTYDEFINITIONS

DIEAREA ( 0 0 ) ( 1304 788 ) ;

PINS 3 ;
- D2_output + NET D2_output
  + DIRECTION INOUT
  + PORT
    + LAYER M1 ( 0 0 ) ( 32 34 )
    + PLACED ( 1078 714 ) N ;
- S + NET S
  + DIRECTION INOUT
  + PORT
    + LAYER M1 ( 0 0 ) ( 54 38 )
    + PLACED ( 620 730 ) N ;
- D1_input + NET D1_input
  + DIRECTION INOUT
  + PORT
    + LAYER M1 ( 0 0 ) ( 16 16 )
    + PLACED ( 230 704 ) N ;
END PINS

BLOCKAGES 1 ;
- LAYER M1
  RECT ( 480 472 ) ( 816 696 ) ;
END BLOCKAGES

NETS 3 ;
- D2_output
  ( PIN D2_output ) ;
- S
  ( PIN S ) ;
- D1_input
  ( PIN D1_input ) ;
END NETS

END DESIGN
"""
    p = DEFParser()
    p.parse( str)

