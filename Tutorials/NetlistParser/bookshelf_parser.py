import re
from collections import namedtuple
from collections import OrderedDict

import json

# Token specification
COMMENT = r'(?P<COMMENT>\#.*\n)'
EOLN = r'(?P<EOLN>\n)'
NUM =  r'(?P<NUM>-?\d*\.\d+|-?\d+\.?)'

SEMI = r'(?P<SEMI>;)'
LPAREN = r'(?P<LPAREN>\()'
RPAREN = r'(?P<RPAREN>\))'
LBRACE = r'(?P<LBRACE>\{)'
RBRACE = r'(?P<RBRACE>\})'
MINUS = r'(?P<MINUS>\-)'
PLUS = r'(?P<PLUS>\+)'
COLON = r'(?P<COLON>\:)'
COMMA = r'(?P<COMMA>\,)'
FSLASH = r'(?P<FSLASH>\/)'

NAME = r'(?P<NAME>[a-zA-Z_][a-zA-Z_!0-9]*)'
LIT =  r'(?P<LIT>\".*?\")'
WS  = r'(?P<WS>\s+)'

master_pat = re.compile('|'.join([COMMENT,EOLN,NUM,SEMI,LPAREN,RPAREN,LBRACE,RBRACE,MINUS,PLUS,COLON,COMMA,FSLASH,NAME,LIT,WS]))

# Tokenizer
Token = namedtuple('Token', ['type','value'])

def generate_tokens(text):
    scanner = master_pat.scanner(text)
    for m in iter(scanner.match, None):
        tok = Token(m.lastgroup, m.group())
        if tok.type != 'WS': # and tok.type != 'COMMENT':
            yield tok

def test_tokenize_two_strings():
    foo = list(generate_tokens( '"Steve" "Burns"'))
    print( foo)
    assert len(foo) == 2
    assert foo[0].type == 'LIT'
    assert foo[1].type == 'LIT'
    assert foo[0].value == '"Steve"'
    assert foo[1].value == '"Burns"'

def test_tokenize_numbers():
    foo = list(generate_tokens( '--6.8 6. .8'))
    print( foo)
    assert len(foo) == 4
    assert foo[0].type == 'MINUS'
    assert foo[1].type == 'NUM'
    assert foo[1].value == '-6.8'
    assert foo[2].type == 'NUM'
    assert foo[2].value == '6.'
    assert foo[3].type == 'NUM'
    assert foo[3].value == '.8'


class Parser:
    '''
    Base class for recursive descent parsers.

    Use the ._accept() method to test and accept the current lookahead token.
    Use the ._accept_keyword() method to test and accept the current
    lookahead token if it matches the argument.
    Use the ._expect() method to exactly match and consume the next token on
    the input (or raise a SyntaxError if it doesn't match).
    Use the ._expect_keyword() method to exactly match and consume the next token on
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

    def parseint( self):
        self._expect( 'NUM')
        return int(self.tok.value)

class Blank:
    def __init__(self):
        pass

class BlocksParser(Parser):
    def pointList( self):
        points = []
        while self._accept( 'LPAREN'):
            x = self.parseint()
            self._expect( 'COMMA')
            y = self.parseint()
            self._expect( 'RPAREN')
            points.append( { "x": x, "y": y})
        return points

    def whole(self):
        b = Blank()
        b.outlines = []
        b.blocks = []
        b.terminals = []

        while True:
            if self._accept( 'EOLN'):
                pass
            elif self._accept( 'COMMENT'):
                pass
            elif self._accept_keyword( 'NumSoftRectangularBlocks'):
                self._expect( 'COLON')
                b.NumSoftRectangularBlocks = self.parseint()
                self._expect( 'EOLN')
            elif self._accept_keyword( 'NumHardRectilinearBlocks'):
                self._expect( 'COLON')
                b.NumHardRectilinearBlocks = self.parseint()
                self._expect( 'EOLN')
            elif self._accept_keyword( 'NumTerminals'):
                self._expect( 'COLON')
                b.NumTerminals = self.parseint()
                self._expect( 'EOLN')
            elif self._accept_keyword( 'BLOCK'):
                self._expect( 'NAME')
                block_nm = self.tok.value
                self._expect( 'COLON')
                n = self.parseint()
                self._expect( 'EOLN')
                pin_lst = []
                for i in range(n):
                    self._expect( 'NAME')
                    pin_name = self.tok.value
                    self._expect( 'NAME')
                    layer = self.tok.value
                    point_lst = self.pointList()
                    assert pin_name not in pin_lst
                    pin_lst.append( { "pin": pin_name, "layer" : layer, "points": point_lst})
                    self._expect( 'EOLN')
                obs_lst = []
                while self._accept_keyword( 'INT'):
                    self._expect( 'NAME')
                    layer = self.tok.value
                    point_lst = self.pointList()
                    point_lst.append( (layer, point_lst))
                    self._expect( 'EOLN')
                assert n == len(pin_lst)
                b.blocks.append( { "block": block_nm, "pins": pin_lst, "obstructions": obs_lst})
            elif self._accept( 'NAME'):
                nm = self.tok.value
                if self._accept_keyword( 'hardrectilinear'):
                    m = self.parseint()
                    point_lst = self.pointList()
                    assert m == len(point_lst)
                    b.outlines.append( { "block": nm, "outline": point_lst})
                    self._expect( 'EOLN')
                else:
                    self._expect( 'NAME')
                    layer = self.tok.value
                    self._expect_keyword( 'terminal')
                    b.terminals.append( { "net": nm, "layer" : layer})
                    self._expect( 'EOLN')

            elif  self.nexttok is None:
                break
            else:
                raise SyntaxError( 'Expected NAME')

        assert b.NumSoftRectangularBlocks == 0
        assert b.NumHardRectilinearBlocks == len( b.blocks)
        assert b.NumHardRectilinearBlocks == len( b.outlines)
        assert b.NumTerminals == len( b.terminals)

        outline_tbl = OrderedDict()
        for outline in b.outlines:
            outline_tbl[outline['block']] = outline

        # Stitch together blocks and outlines
        for block in b.blocks:
            block['outline'] = outline_tbl[block['block']]

        return { "blocks": b.blocks,
                 "terminals": b.terminals}

class NetsParser(Parser):
    def whole(self):
        b = Blank()
        b.nets = OrderedDict()

        while True:
            if self._accept( 'EOLN'):
                pass
            elif self._accept( 'COMMENT'):
                pass
            elif self._accept_keyword( 'NumNets'):
                self._expect( 'COLON')
                b.NumNets = self.parseint()
                self._expect( 'EOLN')
            elif self._accept_keyword( 'NumPins'):
                self._expect( 'COLON')
                b.NumPins = self.parseint()
                self._expect( 'EOLN')
            elif self._accept( 'NAME'):
                nm = self.tok.value
                self._expect( 'COLON')
                n = self.parseint()
                self._expect( 'EOLN')

                b.nets[nm] = []
                for i in range(n):
                    self._expect( 'NAME')
                    instance_nm = self.tok.value
                    self._expect( 'NAME')
                    pin_nm = self.tok.value
                    b.nets[nm].append( (instance_nm, pin_nm))
                    self._expect( 'EOLN')
                
            elif  self.nexttok is None:
                break
            else:
                raise SyntaxError( 'Expected NAME')

        return { "NumNets": b.NumNets, "NumPins": b.NumPins, "nets": b.nets}


class PlParser(Parser):
    def bracePoint(self):
        self._expect( 'LBRACE')
        x = self.parseint()
        self._expect( 'COMMA')
        y = self.parseint()
        self._expect( 'RBRACE')
        return (x,y)

    def whole(self):
        b = Blank()
        b.instances = OrderedDict()
        b.terminals = OrderedDict()
        while True:
            if self._accept( 'EOLN'):
                pass
            elif self._accept( 'COMMENT'):
                pass
            elif self._accept_keyword( 'DIE'):
                ll = self.bracePoint()
                ur = self.bracePoint()
                b.bbox = (ll,ur)
                self._expect( 'EOLN')
            elif self._accept( 'NAME'):
                nm = self.tok.value
                x = self.parseint()
                y = self.parseint()
                if self._accept( 'NAME'):
                    t = self.tok.value
                    b.instances[nm] = (x,y,t)
                else:
                    b.terminals[nm] = (x,y)

                self._expect( 'EOLN')
            elif  self.nexttok is None:
                break
            else:
                raise SyntaxError( 'Expected NAME')

        return { "bbox": b.bbox, "instances": b.instances, "terminals": b.terminals}

class ConstsParser(Parser):
    def parseHierName(self):
        lst = []
        self._expect( 'NAME')
        lst.append( self.tok.value)
        while self._accept( 'FSLASH'):
            self._expect( 'NAME')
            lst.append( self.tok.value)
        return lst

    def braceTuple(self):
        lst = []
        self._expect( 'LBRACE')
        lst.append( self.parseHierName())
        while self._accept( 'COMMA'):
            lst.append( self.parseHierName())
        self._expect( 'RBRACE')
        return lst

    def whole(self):
        b = Blank()
        b.symmnets = []
        b.critnets = OrderedDict()
        b.shieldnets = []
        b.matchblocks = []
        while True:
            if self._accept( 'EOLN'):
                pass
            elif self._accept( 'COMMENT'):
                pass
            elif self._accept_keyword( 'SymmNet'):
                self._expect( 'LPAREN')
                t0 = self.braceTuple()
                self._expect( 'COMMA')
                t1 = self.braceTuple()
                self._expect( 'RPAREN')
                b.symmnets.append( (t0,t1))
                self._expect( 'EOLN')
            elif self._accept_keyword( 'CritNet'):
                self._expect( 'LPAREN')
                self._expect( 'NAME')
                net_nm = self.tok.value
                self._expect( 'COMMA')
                self._expect( 'NAME')
                priority = self.tok.value
                self._expect( 'RPAREN')
                self._expect( 'EOLN')
                b.critnets[net_nm] = priority
            elif self._accept_keyword( 'ShieldNet'):
                self._expect( 'LPAREN')
                self._expect( 'NAME')
                net_nm = self.tok.value
                self._expect( 'RPAREN')
                self._expect( 'EOLN')
                b.shieldnets.append( net_nm)
            elif self._accept_keyword( 'MatchBlock'):
                self._expect( 'LPAREN')
                self._expect( 'NAME')
                b0 = self.tok.value
                self._expect( 'COMMA')
                self._expect( 'NAME')
                b1 = self.tok.value
                self._expect( 'RPAREN')
                self._expect( 'EOLN')
                b.matchblocks.append( (b0,b1))
            elif  self.nexttok is None:
                break
            else:
                raise SyntaxError( 'Expected SymmNet, CritNet, ShieldNet, or MatchBlock keyword.')
        return { "symmnets": b.symmnets, "critnets": b.critnets, "shieldnets": b.shieldnets, "matchblocks": b.matchblocks}

def test_blocks():

    s = """#UMN blocks 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumSoftRectangularBlocks : 0
NumHardRectilinearBlocks : 3
NumTerminals : 5

L1_MM4_MM5	hardrectilinear 4 (0, 0) (0, 789) (648, 789) (648, 0)
L1_MM1_MM0	hardrectilinear 4 (0, 0) (-0, 842) (648, 842) (648, 0)
L1_MM3_MM2	hardrectilinear 4 (-0, 0) (0, 789) (648, 789) (648, 0)


BLOCK L1_MM4_MM5 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (196, 748)	(196,	788)	(236, 788)	(236,	748)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789)	(196, 789)
INT M1 (412, 619) (412, 789) (452, 789)	(412, 789)



BLOCK L1_MM1_MM0 : 5
G1	M1 (108, 684)	(108,	842)	(148, 842)	(148,	684)
G2	M1 (504, 684)	(504,	836)	(544, 836)	(544,	684)
D1	M1 (88,   4)	(88,   146)	(128, 146)	(128,	4)
S	M1 (236, 796)	(236,	836)	(412, 836)	(412,	796)
D2	M1 (520,   -0)	(520,	146)	(560, 146)	(560,	0)
INT M1 (196, 612) (196,	836) (236, 836)	(196, 836)
INT M1 (412, 612) (412,	836) (452, 836)	(412, 836)



BLOCK L1_MM3_MM2 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (236, 749)	(236,	789)	(412, 789)	(412,	749)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789) (236, 619)
INT M1 (412, 619) (412, 789) (452, 789) (452, 619)
INT M1 (89, 39) (89, 148) (125, 148) (125, 39)
INT M1 (89, 39) (89, 75) (471, 75) (471, 39)


gnd!	M1 terminal
vdd!	M1 terminal
net2	M1 terminal
net14	M1 terminal
net17	M1 terminal
"""

#    print( list(generate_tokens( s)))
    p = BlocksParser()
    print( json.dumps( p.parse( s), indent=2) + '\n')

def test_nets():
    s = """#UMN nets 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumNets : 8
NumPins : 11

net2 : 2
L1_MM3_MM2 D1
terminal net2
net8 : 2
L1_MM4_MM5 D1
L1_MM1_MM0 D1
net10 : 2
L1_MM3_MM2 D2
L1_MM1_MM0 S
net11 : 2
L1_MM4_MM5 D2
L1_MM1_MM0 D2
net14 : 2
terminal net14
L1_MM1_MM0 G2
net17 : 2
terminal net17
L1_MM1_MM0 G1
gnd! : 2
L1_MM3_MM2 S
terminal gnd!
vdd! : 2
L1_MM4_MM5 S
terminal vdd!
"""

#    print( list(generate_tokens( s)))
    p = NetsParser()
    print( json.dumps( p.parse( s), indent=2) + '\n')


def test_pl():
    s = """# TAMU blocks 1.0

DIE {0, 0} {648, 2620}

L1_MM4_MM5	0	0	N
L1_MM1_MM0	648	889	FN
L1_MM3_MM2	0	2620	FS

net2	648	1932
net14	0	1649
net17	648	1652
gnd!	0	1851
vdd!	0	768
"""

#    print( list(generate_tokens( s)))
    p = PlParser()
    print( json.dumps( p.parse( s), indent=2) + '\n')


def test_consts():
    s = """SymmNet ( {net8,L1_MM1_MM0/D1,L1_MM4_MM5/D1} , {net11,L1_MM1_MM0/D2,L1_MM4_MM5/D2} )
SymmNet ( {net17,L1_MM1_MM0/G1,net17} , {net14,L1_MM1_MM0/G2,net14} )
CritNet ( net8 , min )
CritNet ( net10 , mid )
"""
#    print( list(generate_tokens( s)))
    p = ConstsParser()
    print( json.dumps( p.parse( s), indent=2) + '\n')

def test_consts_sc():
    s = """CritNet(net7, min)
CritNet(net23, min)
SymmNet({Voutn,L1_CC0_CC2/CN2,L0_MM7/D,I0/Voutn},{Voutp,L1_CC0_CC2/CN1,L0_MM8/S,I0/Voutp})
SymmNet({net7,L1_CC5_CC7/CP2,L1_CC0_CC2/CP2,I0/Vinp,L0_MM3/D},{net23,L1_CC5_CC7/CP1,L1_CC0_CC2/CP1,I0/Vinn,L0_MM1/S})
SymmNet({net11,L0_MM6/D,L0_MM7/S,L1_CC1_CC3/CN1},{net12,L0_MM11/S,L0_MM8/D,L1_CC1_CC3/CN2})
SymmNet({net5,L1_CC4_CC6/CP2,L1_CC1_CC3/CP1,L0_MM5/D,L0_MM3/S},{net6,L1_CC4_CC6/CP1,L1_CC1_CC3/CP2,L0_MM9/S,L0_MM1/D})
SymmNet({net4,L1_CC4_CC6/CN2,L0_MM2/D,L0_MM4/D},{net3,L1_CC4_CC6/CN1,L0_MM0/S,L0_MM10/S})
SymmNet({Vinn,L1_CC5_CC7/CN1,L0_MM2/S},{Vinp,L1_CC5_CC7/CN2,L0_MM0/D})
ShieldNet(Vinn)
ShieldNet(Vinp)
ShieldNet(net3)
ShieldNet(net4)
ShieldNet(net5)
ShieldNet(net6)
ShieldNet(net7)
ShieldNet(net23)
MatchBlock(L0_MM0,L0_MM2)
MatchBlock(L0_MM10,L0_MM4)
MatchBlock(L0_MM9,L0_MM5)
MatchBlock(L0_MM3,L0_MM1)
MatchBlock(L0_MM6,L0_MM11)
MatchBlock(L0_MM7,L0_MM8)
"""
#    print( list(generate_tokens( s)))
    p = ConstsParser()
    print( json.dumps( p.parse( s), indent=2) + '\n')
