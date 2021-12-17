
import re
import collections

# Token specification
pats = []
pats.append( r'(?P<SEMI>;)')
pats.append( r'(?P<NAME>[a-zA-Z_][a-zA-Z_0-9]*)')
pats.append( r'(?P<NUM>[-+]?\d*\.\d+|[-+]?\d+\.?)')
pats.append( r'(?P<LIT>\".*\")')
pats.append( r'(?P<WS>\s+)')

master_pat = re.compile('|'.join(pats))

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

def generate_tokens(text):
    scanner = master_pat.scanner(text)
    for m in iter(scanner.match, None):
        tok = Token(m.lastgroup, m.group())
        if tok.type != 'WS':
            yield tok

class Macro:
    def __init__(self):
        self.pins = None
        self.obs = None
        self.scale_factor = 10000

    def prnt(self):
        # print( f"macroName {self.macroName} ox {self.ox} oy {self.oy} sx {self.sx} sy {self.sy} bbox {self.bbox}")
        for pin in self.pins:
            pin.prnt()
        self.obs.prnt()

    @property
    def bbox(self):
        return [self.ox, self.oy, self.ox+self.sx, self.oy+self.sy]

class Pin:
    def __init__(self):
        pass

    def prnt(self):
        print( '   pin', self.nm, self.direction)
        for port in self.ports:
            print( '      port', port)

class Obs:
    def __init__(self):
        pass

    def prnt(self):
        print( '   obs')
        for port in self.ports:
            print( '      port', port)


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
#        print( self.tok, self.nexttok)

    def _accept(self,toktype):
        'Test and consume the next token if it matches toktype'
        if self.nexttok and self.nexttok.type == toktype:
            self._advance()
            return True
        else:
            return False

    def _accept_keyword(self,k):
        'Test and consume the next token if it matches the keyword k'
        if self.nexttok and self.nexttok.type == 'NAME' and self.nexttok.value == k:
            self._advance()
            return True
        else:
            return False

    def _expect(self,toktype):
        'Consume next token if it matches toktype or raise SyntaxError'
        if not self._accept(toktype):
            raise SyntaxError('Expected ' + toktype)

    def _expect_keyword(self,k):
        'Consume next token if it matches argument or raise SyntaxError'
        if not self._accept_keyword(k):
            raise SyntaxError('Expected keyword' + k)

    def pA( self, m):
        self._expect('NUM')
        return float(self.tok.value)

    # Grammar rules follow
    def ports(self, m, pin):
        pin.ports = []
        layer = None
        while True:
            if self._accept_keyword( 'END'):
                break
            elif self._accept_keyword( 'LAYER'):
                self._expect('NAME')
                layer = self.tok.value
                self._expect('SEMI')
            elif self._accept_keyword( 'RECT'):
                lst = [ self.pA(m) for _ in range(4)]
                self._expect('SEMI')
                assert layer is not None
                pin.ports.append( ( layer, tuple(lst)))
            else:
                raise SyntaxError('Expected END, LAYER, or RECT keywords.')

    def macro(self):
        m = Macro()
        m.pins = []

        self._expect('NAME')
        m.macroName = self.tok.value
        while True:
            if self._accept_keyword( 'END'):
                self._expect_keyword(m.macroName)
                break
            elif self._accept_keyword( 'ORIGIN'):
                m.ox = self.pA(m)
                m.oy = self.pA(m)
                self._expect('SEMI')
            elif self._accept_keyword( 'FOREIGN'):
                self._expect('NAME')
                m.foreign_name = self.tok.value
                m.fx = self.pA(m)
                m.fy = self.pA(m)
                self._expect('SEMI')
            elif self._accept_keyword( 'SIZE'):
                m.sx = self.pA(m)
                self._expect_keyword('BY')
                m.sy = self.pA(m)
                self._expect('SEMI')
            elif self._accept_keyword( 'PIN'):
                pin = Pin()
                self._expect('NAME')
                pin.nm = self.tok.value
                while True:
                    if self._accept_keyword( 'END'):
                        self._expect_keyword(pin.nm)
                        break
                    elif self._accept_keyword( 'DIRECTION'):
                        self._expect('NAME')
                        pin.direction = self.tok.value
                        self._expect('SEMI')
                    elif self._accept_keyword( 'USE'):
                        self._expect('NAME')
                        self._expect('SEMI')
                    elif self._accept_keyword( 'PORT'):
                        self.ports(m, pin)
                    else:
                        raise SyntaxError('Expected END, DIRECTION, USE, or PORT keywords.')
                m.pins.append(pin)
            elif self._accept_keyword( 'UNITS'):
                self._expect_keyword( 'DATABASE')
                self._expect_keyword('MICRONS')
                self._expect_keyword('UNITS')
                self._expect('NUM')
                m.scale_factor = float(self.tok.value)
                self._expect('SEMI')
                self._expect_keyword( 'END')
                self._expect_keyword('UNITS')
            elif self._accept_keyword( 'OBS'):
                m.obs = Obs()
                self.ports( m, m.obs)
            elif self._accept_keyword( 'PROPERTY'):
                self._expect('NAME')
                if self._accept( 'LIT') or self._accept( 'NUM'):
                    self._expect('SEMI')
                else:
                    raise SyntaxError('Expected LIT or NUM tokens')
            else:
                self._expect('NAME')

        return m

    def whole(self):

        self.macros = []

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
                m = self.macro()
                self.macros.append(m)
            elif self.nexttok is None:
                break
            else:
                raise SyntaxError( f'Expected END, VERSION, BUSBITCHARS, DIVIDERCHAR, PROPERTYDEFINITIONS or MACRO, got {self.nexttok}')
