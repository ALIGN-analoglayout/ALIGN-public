
import re
import collections

# Token specification
pats = []
pats.append( r'(?P<DOUBLESLASH>//)')
pats.append( r'(?P<SEMI>;)')
pats.append( r'(?P<PERIOD>\.)')
pats.append( r'(?P<BAR>\|)')
pats.append( r'(?P<BANG>!)')
pats.append( r'(?P<COMMA>,)')
pats.append( r'(?P<BACKTICK>`)')
pats.append( r'(?P<LPAREN>\()')
pats.append( r'(?P<RPAREN>\))')
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

class Instance:
    def __init__(self):
        self.template_name = None
        self.instance_name = None
        self.fa_list = None

    def prnt(self):
        print( f"{self.template_name} {self.instance_name} ( {','.join(map(str,self.fa_list))} )")

class Module:
    def __init__(self):
        self.nm = None
        self.parameters = None
        self.outputs = []
        self.inputs = []
        self.instances = []

    def prnt(self):
        print( f"module {self.nm} ( {','.join( self.parameters)} )")
        print( f"inputs {','.join(self.inputs)}")
        print( f"outputs {','.join(self.outputs)}")
        for inst in self.instances:
            inst.prnt()

# Parser 
class VerilogParser:
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
        print("Parsing", text)
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


    def parse_hier_name(self):
        result = []
        result.append(self.parse_name())
        while self._accept('BAR'):
            result.append( self.parse_name())
        return '|'.join(result)

    def parse_fa_pair(self):
        self._expect('PERIOD')
        self._expect('NAME')
        formal = self.tok.value
        self._expect('LPAREN')
        self._expect('NAME')
        actual = self.tok.value
        self._expect('RPAREN')
        return (formal,actual)

    def parse_possibly_empty_comma_separated_list(self, f):
        result = []
        self._expect('LPAREN')
        if self._accept('RPAREN)'):
            pass
        else:
            result.append( f())
            while self._accept('COMMA'):
                result.append( f())
            self._expect('RPAREN')
        return result

    def parse_comma_separated_list(self, f):
        result = []
        result.append( f())
        while self._accept('COMMA'):
            result.append( f())
        return result

    def parse_name(self):
        self._expect('NAME')
        return self.tok.value

    def whole(self):

        while True:
            if self.nexttok is None:
                break
            elif self._accept_keyword('module'):
                m = Module()
                self._expect('NAME')
                m.nm = self.tok.value
                m.parameters = self.parse_possibly_empty_comma_separated_list( self.parse_name)
                self._expect('SEMI')                            
                
                while True:
                    if self._accept_keyword( 'input') or self._accept_keyword( 'output'):
                        ty = self.tok.value
                        nms = self.parse_comma_separated_list( self.parse_name)
                        if ty == 'input':
                            m.inputs += nms
                        elif ty == 'output':
                            m.outputs += nms
                        else:
                            assert False, ty
                        self._expect('SEMI')
                    elif self._accept_keyword( 'endmodule'):
                        m.prnt()
                        break
                    else:
                        inst = Instance()
                        m.instances.append(inst)
                        inst.template_name = self.parse_name()
                        inst.instance_name = self.parse_hier_name()
                        inst.fa_list = self.parse_possibly_empty_comma_separated_list( self.parse_fa_pair)
                        self._expect('SEMI')                            
                        
            else:
                raise SyntaxError( f'Expected module, got {self.nexttok}')
            
