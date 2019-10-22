import collections
import re

from .core import Circuit
from .elements import library

# Token specification
pats = []
pats.append( r'(?P<COMMENT>\s*;[^\n\r]*)')
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

    def _nexttoken(self):
        'Advance one token ahead'
        return next(self._tokens, None)

    def parse(self, text):
        self._tokens = self._generate_tokens(text)
        tok = self._nexttoken()
        if tok.type == 'PLUS':
            self._cache_statement()
        elif tok.type == 'DECL':
            self._dispatch()
            self._process_declaration(tok.value)
        else:
            self._dispatch()
            self._process_instance(tok.value)

    def _cache():
        if self._instance_cache is not None:
            cache = self._instance_cache
        elif self._declaration_cache is not None:
            cache = self._declaration_cache
        else:
            raise AssertionError
        tok = self._nexttoken()
        while tok is not None:
            cache.append(tok)
            tok = self._nexttoken()

    def _dispatch():
        if self._instance_cache is not None:
            pass
        if self._declaration_cache is not None:
            pass
