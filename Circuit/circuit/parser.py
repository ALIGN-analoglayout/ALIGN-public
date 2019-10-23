import collections
import re

from .core import Circuit
from .elements import Library

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

    def __init__(self):
        self.library = Library()
        self.circuit = Circuit()

    @staticmethod
    def _generate_tokens(text):
        scanner = spice_pat.scanner(text)
        for m in iter(scanner.match, None):
            tok = Token(m.lastgroup, m.group())
            if tok.type not in ['WS', 'COMMENT', 'CONTINUE', 'EMPTY']:
                yield tok

    def parse(self, text):
        cache = []
        for tok in self._generate_tokens(text):
            if tok.type == 'NEWL':
                self._dispatch(cache)
                cache.clear()
            else:
                cache.append(tok)
        self._dispatch(cache)

    def _dispatch(self, cache):
        if len(cache) == 0:
            return
        token = cache.pop(0)
        args, kwargs = self._decompose(cache)
        if token.type == 'NAME':
            self._process_instance(token.value, args, kwargs)
        elif token.type == 'DECL':
            self._process_declaration(token.value, args, kwargs)
        else:
            raise AssertionError(cache, "must begin with DECL or NAME")

    def _decompose(self, cache):
        assert all(x.type in ('NAME', 'NUM', 'EQUALS') for x in cache)
        assignments = {i for i, x in enumerate(cache) if x.type == 'EQUALS'}
        assert all(cache[i-1].type == 'NAME' for i in assignments)
        args = [x.value for i, x in enumerate(cache) if len(assignments.intersection({i-1, i, i+1})) == 0]
        kwargs = {cache[i-1].value: cache[i+1].value for i in assignments}
        return args, kwargs

    def _process_instance(self, name, args, kwargs):
        defaults = {'C': 'CAP', 'R': 'RES'}
        if any(name.startswith(x) for x in ('C', 'R', 'L')):
            model = defaults[name[0]]
            kwargs['value'] = args.pop()
        elif any(name.startswith(x) for x in ('M', 'X')):
            model = args.pop()
        else:
            raise NotImplementedError(name, args, kwargs, "is not yet recognized by parser")

        assert model in self.library, (model, name, args, kwargs)
        self.circuit.add_element(self.library[model](name, *args, **kwargs))

    def _process_declaration(self, decl, args, kwargs):
        pass