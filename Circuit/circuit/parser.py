import collections
import re

from .core import Circuit, SubCircuit, Model
from .elements import Library

# Token specification
pats = []
pats.append( r'(?P<NLCOMMENT>(^|[\n\r])+\*[^\n\r]*)')
pats.append( r'(?P<COMMENT>\s*;[^\n\r]*)')
pats.append( r'(?P<CONTINUE>(^|[\n\r])+\+)')
pats.append( r'(?P<NEWL>[\n\r]+)')
pats.append( r'(?P<TOKEN>[A-Z0-9!_\.\-]+)')
pats.append( r'(?P<EQUALS>\s*=\s*)')
pats.append( r'(?P<WS>\s+)')

# re.IGNORECASE is not required since everything is capitalized prior to tokenization
spice_pat = re.compile('|'.join(pats))

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

class SpiceParser:

    _context = []

    def __init__(self):
        self.library = Library()
        self.circuit = Circuit()
        self._scope = [self.circuit]

    @staticmethod
    def _generate_tokens(text):
        scanner = spice_pat.scanner(text.upper())
        for m in iter(scanner.match, None):
            tok = Token(m.lastgroup, m.group())
            if tok.type in ['TOKEN', 'NEWL', 'EQUALS']:
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
        assert token.type == 'TOKEN', token
        args, kwargs = self._decompose(cache)
        if token.value.startswith('.'):
            self._process_declaration(token.value, args, kwargs)
        else:
            self._process_instance(token.value, args, kwargs)

    @staticmethod
    def _decompose(cache):
        assert all(x.type in ('TOKEN', 'EQUALS') for x in cache)
        assignments = {i for i, x in enumerate(cache) if x.type == 'EQUALS'}
        assert all(cache[i-1].type == 'TOKEN' for i in assignments)
        args = [x.value for i, x in enumerate(cache) if len(assignments.intersection({i-1, i, i+1})) == 0]
        kwargs = {cache[i-1].value: cache[i+1].value for i in assignments}
        return args, kwargs

    def _process_instance(self, name, args, kwargs):
        defaults = {'C': 'CAP', 'R': 'RES', 'L': 'IND'}
        if any(name.startswith(x) for x in ('C', 'R', 'L')):
            model = defaults[name[0]]
            kwargs['VALUE'] = args.pop()
        elif any(name.startswith(x) for x in ('M', 'X')):
            model = args.pop()
        else:
            raise NotImplementedError(name, args, kwargs, "is not yet recognized by parser")

        assert model in self.library, (model, name, args, kwargs)
        self._scope[-1].add_element(self.library[model](name, *args, **kwargs))

    def _process_declaration(self, decl, args, kwargs):
        if decl == '.SUBCKT':
            name = args.pop(0)
            subckt = SubCircuit(name, *args, library=self.library, **kwargs)
            self._scope.append(subckt)
        elif decl == '.ENDS':
            self._scope.pop()
        elif decl == '.PARAM':
            assert len(args) == 0
            self._scope[-1].add_parameters(kwargs)
        elif decl == '.MODEL':
            assert len(args) == 2, args
            name, type_ = args[0], args[1]
            assert type_ in self.library, type_
            Model(name, self.library[type_], library=self.library, **kwargs)