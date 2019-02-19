
import re
from collections import namedtuple

pats = []
pats.append( r'(?P<NAME>[a-zA-Z_][a-zA-Z_0-9]*)')
pats.append( r'(?P<NUM>\d+)')
pats.append( r'(?P<PLUS>\+)')
pats.append( r'(?P<TIMES>\*)')
pats.append( r'(?P<EQ>=)')
pats.append( r'(?P<WS>\s+)')

master_pat = re.compile('|'.join(pats))

Token = namedtuple('Token', ['type','value'])

def generate_tokens(pat, text):
    scanner = pat.scanner(text)
    for m in iter(scanner.match, None):
        yield Token(m.lastgroup, m.group())

for tok in generate_tokens(master_pat, 'foo = 42'):
    print(tok)
