
import re
import collections

# Token specification
pats = []
pats.append( r'(?P<SEMI>;)')
pats.append( r'(?P<COMMA>\,)')
pats.append( r'(?P<LBRC>\{)')
pats.append( r'(?P<RBRC>\})')
pats.append( r'(?P<NAME>[a-zA-Z_][a-zA-Z_0-9|]*)')
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


# Parser 
class PLParser:
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

    def pA(self):
        self._expect('NUM')
        return int(self.tok.value)*5

    def whole(self):

        self.die = []
        self.lst = []

        self._expect_keyword('DIE')
        self._expect('LBRC')
        self.die.append( self.pA())
        self._expect('COMMA')
        self.die.append( self.pA())
        self._expect('RBRC')
        self._expect('LBRC')
        self.die.append( self.pA())
        self._expect('COMMA')
        self.die.append( self.pA())
        self._expect('RBRC')

        portPhase = False

        while self._accept('NAME'):
            nm = self.tok.value
            x = self.pA()
            y = self.pA()
            transform = None
            if not portPhase and (self._accept_keyword('N') or self._accept_keyword('FN') or self._accept_keyword('S') or self._accept_keyword('FS')):
                transform = self.tok.value
            else:
                portPhase = True
            self.lst.append( (nm,x,y,transform))

        assert self.nexttok is None
