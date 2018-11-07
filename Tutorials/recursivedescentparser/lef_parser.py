# example.py
#
# An example of writing a simple recursive descent parser

import re
import collections

# Token specification
SEMI = r'(?P<SEMI>;)'
NAME = r'(?P<NAME>[a-zA-Z_][a-zA-Z_0-9]*)'
NUM =  r'(?P<NUM>[-+]?\d*\.\d+|[-+]?\d+\.?)'
LIT =  r'(?P<LIT>\".*\")'
WS     = r'(?P<WS>\s+)'

master_pat = re.compile('|'.join([SEMI,NAME,NUM,LIT,WS]))

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

def generate_tokens(text):
    scanner = master_pat.scanner(text)
    for m in iter(scanner.match, None):
        tok = Token(m.lastgroup, m.group())
        if tok.type != 'WS':
            yield tok

# Parser 
class LEFParser:
    '''
    Implementation of a recursive descent parser for LEF.   Each method
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
        print( self.tok, self.nexttok)

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

    def whole(self):

        while True:
            if self._accept_keyword('END'):
                self._accept_keyword('LIBRARY')
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
            elif self._accept_keyword( 'PROPERTYDEFINITIONS'):
                while True:
                    if self._accept_keyword('END'):
                        self._accept_keyword('PROPERTYDEFINITIONS')
                        break
                    elif self._accept_keyword( 'MACRO'):
                        self._expect('NAME')
                        self._expect('NAME')
                        self._expect('SEMI')
                    else:
                        raise SyntaxError('Expected END or MACRO keywords')
            elif self._accept_keyword( 'MACRO'):
                self._expect('NAME')
                macroName = self.tok.value 
                while True:
                    if self._accept_keyword( 'END'):
                        self._expect_keyword(macroName)
                        break
                    elif self._accept_keyword( 'ORIGIN'):
                        self._expect('NUM')
                        self._expect('NUM')
                        self._expect('SEMI')
                    elif self._accept_keyword( 'FOREIGN'):
                        self._expect('NAME')
                        self._expect('NUM')
                        self._expect('NUM')
                        self._expect('SEMI')
                    elif self._accept_keyword( 'SIZE'):
                        self._expect('NUM')
                        self._expect_keyword('BY')
                        self._expect('NUM')
                        self._expect('SEMI')
                    elif self._accept_keyword( 'PIN'):
                        self._expect('NAME')
                        pinName = self.tok.value
                        while True:
                            if self._accept_keyword( 'END'):
                                self._expect_keyword(pinName)
                                break
                            elif self._accept_keyword( 'DIRECTION'):
                                self._expect('NAME')
                                self._expect('SEMI')    
                            elif self._accept_keyword( 'USE'):
                                self._expect('NAME')
                                self._expect('SEMI')    
                            elif self._accept_keyword( 'PORT'):
                                while True:
                                    if self._accept_keyword( 'END'):
                                        break
                                    elif self._accept_keyword( 'LAYER'):
                                        self._expect('NAME')
                                        self._expect('SEMI')    
                                    elif self._accept_keyword( 'RECT'):
                                        self._expect('NUM')
                                        self._expect('NUM')
                                        self._expect('NUM')
                                        self._expect('NUM')
                                        self._expect('SEMI')    
                                    else:
                                        raise SyntaxError('Expected END, LAYER, or RECT keywords.')     
                            else:
                                raise SyntaxError('Expected END, DIRECTION, USE, or PORT keywords.')     

                                        
                    elif self._accept_keyword( 'OBS'):
                        while True:
                            if self._accept_keyword( 'END'):
                                break
                            elif self._accept_keyword( 'LAYER'):
                                self._expect('NAME')
                                self._expect('SEMI')    
                            elif self._accept_keyword( 'RECT'):
                                self._expect('NUM')
                                self._expect('NUM')
                                self._expect('NUM')
                                self._expect('NUM')
                                self._expect('SEMI')    
                            else:
                                raise SyntaxError('Expected END, LAYER, or RECT keywords.')     
                    elif self._accept_keyword( 'PROPERTY'):
                        self._expect('NAME')
                        if self._accept( 'LIT') or self._accept( 'NUM'):
                            self._expect('SEMI')                                
                        else:
                            raise SyntaxError('Expected LIT or NUM tokens')
                    else:
                        self._expect('NAME')

            else:
                raise SyntaxError( 'Expected END, VERSION, BUSBITCHARS, DIVIDERCHAR, PROPERTYDEFINITIONS or MACRO')

def test_lef():
    str = """VERSION 5.7 ;
BUSBITCHARS "[]" ;
DIVIDERCHAR "/" ;

PROPERTYDEFINITIONS
  MACRO function STRING ;
  MACRO _pcCompiledCounter INTEGER ;
  MACRO viewSubType STRING ;
END PROPERTYDEFINITIONS

MACRO current_mirror_nmos
  ORIGIN 0 0 ;
  FOREIGN current_mirror_nmos 0 0 ;
  SIZE 0.326 BY 0.197 ;
  PIN D2_output
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M1 ;
        RECT 0.2695 0.1785 0.2775 0.187 ;
    END
  END D2_output
  PIN S
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M1 ;
        RECT 0.155 0.1825 0.1685 0.192 ;
    END
  END S
  PIN D1_input
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M1 ;
        RECT 0.0575 0.176 0.0615 0.18 ;
    END
  END D1_input
  OBS
    LAYER M1 ;
      RECT 0.12 0.118 0.204 0.174 ;
  END
  PROPERTY function "transistor" ;
  PROPERTY _pcCompiledCounter 846 ;
  PROPERTY viewSubType "maskLayoutParamCell" ;
END current_mirror_nmos

END LIBRARY
"""
    lp = LEFParser()
    lp.parse( str)

