import collections
import re
import logging

from .core import Circuit, SubCircuit, Model
from . import library
from . import elements
from . import constraint

logger = logging.getLogger(__name__)

unit_multipliers = {
    'T': 1e12,
    'G': 1e9,
    'X': 1e6,
    'MEG': 1e6,
    'K': 1e3,
    'M': 1e-3,
    'U': 1e-6,
    'N': 1e-9,
    'P': 1e-12,
    'F': 1e-15
}

def str2float(val):
    unit = next((x for x in unit_multipliers if val.endswith(x.upper()) or val.endswith(x.lower())), None)
    numstr = val if unit is None else val[:-1*len(unit)]
    return float(numstr) * unit_multipliers[unit] if unit is not None else float(numstr)

# Token specification
modifiers = '|'.join(unit_multipliers.keys())
numericval = fr'[+-]?(?:0|[1-9]\d*)(?:[.]\d+)?(?:E[+\-]?\d+)?(?:{modifiers})?'
identifier = r'[^\s{}()=;*]+'
operator = r'\s*[*+-/%]\s*'
exprcontent = fr'(?:{numericval}|{identifier})(?:{operator}(?:{numericval}|{identifier}))*'
commentchars = r'(?:[;$]|//)'

token_re_map = {
    'ANNOTATION': fr'(^|\s)*(\*|{commentchars})+\s*\@:\s*[^\n\r]*',
    'NLCOMMENT': r'(^|[\n\r])+\*[^\n\r]*',
    'COMMENT': fr'(^|\s)*{commentchars}[^\n\r]*',
    'CONTINUE': r'(^|[\n\r])+\+',
    'NEWL': r'[\n\r]+',
    'EQUALS': r'\s*=\s*',
    'EXPR': fr"""(?P<quote>['"]){exprcontent}(?P=quote)|({{){exprcontent}(}})""",
    'NUMBER': numericval + fr'(?=\s|\Z|{commentchars})',
    'DECL': fr'\.{identifier}',
    'NAME': identifier,
    'WS': r'\s+'}
spice_pat = re.compile('|'.join(fr'(?P<{x}>{y})' for x, y in token_re_map.items()), flags=re.IGNORECASE)

constraint_dict = {x: getattr(constraint, x) for x in dir(constraint) if not x.startswith('_')}

# Tokenizer
Token = collections.namedtuple('Token', ['type','value'])

class SpiceParser:

    _context = []

    def __init__(self, mode='Xyce'):
        self.mode = mode.lower()
        assert self.mode in ('xyce', 'hspice')
        self.library = library.Library()
        self.library.update(library.default)
        self.circuit = Circuit()
        self._scope = [self.circuit]

    @staticmethod
    def _generate_tokens(text):
        scanner = spice_pat.scanner(text)
        for m in iter(scanner.match, None):
            tok = Token(m.lastgroup, m.group())
            if tok.type in ['EXPR', 'NUMBER', 'DECL', 'NAME', 'NEWL', 'EQUALS', 'ANNOTATION']:
                yield tok

    def parse(self, text):
        cache = []
        for tok in self._generate_tokens(text):
            if tok.type == 'NEWL':
                self._dispatch(cache)
                cache.clear()
            elif tok.type == 'ANNOTATION':
                self._dispatch(cache)
                cache.clear()
                constraint = self._extract_constraint(tok.value)
                self._process_constraint(constraint)
            else:
                cache.append(tok)
        self._dispatch(cache)

    def _dispatch(self, cache):
        if len(cache) == 0:
            return
        token = cache.pop(0)
        args, kwargs = self._decompose(cache)
        if token.type == 'DECL':
            self._process_declaration(token.value.upper(), args, kwargs)
        elif token.type == 'NAME':
            self._process_instance(token.value.upper(), args, kwargs)
        else:
            assert False

    @staticmethod
    def _extract_constraint(annotation):
        return annotation.split('@:')[1].strip()

    @staticmethod
    def _decompose(cache):
        assert all(x.type in ('NAME', 'NUMBER', 'EXPR', 'EQUALS') for x in cache), cache
        assignments = {i for i, x in enumerate(cache) if x.type == 'EQUALS'}
        assert all(cache[i-1].type == 'NAME' for i in assignments)
        args = [SpiceParser._cast(x.value.upper(), x.type) for i, x in enumerate(cache) if len(assignments.intersection({i-1, i, i+1})) == 0]
        kwargs = {cache[i-1].value.upper(): SpiceParser._cast(cache[i+1].value.upper(), cache[i+1].type) for i in assignments}
        return args, kwargs

    @staticmethod
    def _cast(val, ty='NUMBER'):
        if ty == 'EXPR':
            # TODO: This needs to be handled better
            return val[1:-1]
        elif ty == 'NAME':
            return val
        # Attempt to cast number to float
        try:
            val = str2float(val)
        except ValueError:
            return val
        # Cast to int if possible
        return int(val) if val.is_integer() else val

    def _process_instance(self, name, args, kwargs):
        defaults = {'C': 'CAP', 'R': 'RES', 'L': 'IND'}
        if any(name.startswith(x) for x in ('C', 'R', 'L')):
            model = defaults[name[0]]
            kwargs['VALUE'] = args.pop()
        elif any(name.startswith(x) for x in ('M', 'X')):
            model = args.pop()
        else:
            raise NotImplementedError(name, args, kwargs, "is not yet recognized by parser")

        pins = [str(x) for x in args]
        assert model in self.library, (model, name, args, kwargs)
        self._scope[-1].add_element(self.library[model](name, *pins, **kwargs))

    def _process_constraint(self, constraint):
        try:
            constraint = eval(constraint, {}, constraint_dict)
        except:
            logger.warning(f'Error parsing constraint {repr(constraint)}')
            return
        assert hasattr(self._scope[-1], 'constraint'), \
            f'Constraint {repr(constraint)} can only be defined within a .SUBCKT \nCurrent scope:{self._scope[-1]}'
        self._scope[-1].constraint.append(constraint)

    def _process_declaration(self, decl, args, kwargs):
        if decl == '.SUBCKT':
            name = args.pop(0)
            assert name not in self.library, f"User is attempting to redeclare {name}"
            subckt = SubCircuit(name=name, pins=args, library=self.library, parameters=kwargs)
            self._scope.append(subckt)
        elif decl == '.ENDS':
            self._scope.pop()
        elif decl == '.PARAM':
            assert len(args) == 0
            self._scope[-1] = subckt = SubCircuit(
                name=self._scope[-1].name,
                pins=self._scope[-1].pins,
                library=self.library,
                parameters=self._scope[-1].parameters.update(kwargs))
        elif decl == '.MODEL':
            assert len(args) == 2, args
            name, base = args[0], args[1]
            assert name not in self.library, f"User is attempting to redeclare {name}"
            assert base in self.library, base
            Model(name=name, base=base, library=self.library, parameters=kwargs)
