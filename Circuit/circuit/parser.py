import collections
import re

from .core import Circuit
from .elements import library

# Token specification
pats = []
pats.append( r'(?P<COMMENT>;.*[\n\r])')
pats.append( r'(?P<EMPTY>^\s+)')
pats.append( r'(?P<CONTINUE>\s*\+)')
pats.append( r'(?P<NEWL>[\n\r]+)')
pats.append( r'(?P<DECL>\.[A-Z]+)')
pats.append( r'(?P<NUM>-?\d+\.?\d*(?:[Ee]-?\d+)?(?:T|G|X|MEG|K|M|U|N|P|F)?)')
pats.append( r'(?P<NAME>[A-Z_0-9]+)')
pats.append( r'(?P<EQUALS>\s*=\s*)')
pats.append( r'(?P<WS>\s+)')

spice_pat = re.compile('|'.join(pats), re.IGNORECASE)

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

class SpiceParser:

    _context = []

    @staticmethod
    def _generate_tokens(text):
        scanner = spice_pat.scanner(text)
        for m in iter(scanner.match, None):
            tok = Token(m.lastgroup, m.group())
            if tok.type not in ['WS', 'COMMENT', 'CONTINUE', 'EMPTY']:
                yield tok

