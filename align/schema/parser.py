import collections
import re
import logging

from .model import Model
from .subcircuit import Circuit, SubCircuit
from .instance import Instance
from .types import set_context
from .library import Library
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
    'CONTINUEBACKSLASH': r'\\\s*[\n\r]',
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
Token = collections.namedtuple('Token', ['type', 'value'])


class SpiceParser:

    _context = []

    def __init__(self, library=None, mode='Xyce'):
        self.mode = mode.lower()
        assert self.mode in ('xyce', 'hspice')
        self.library = Library(loadbuiltins=True) if library is None else library
        with set_context(self.library):
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
        self._constraints = None
        for tok in self._generate_tokens(text):
            if tok.type == 'NEWL':
                self._dispatch(cache)
                cache.clear()
            elif tok.type == 'ANNOTATION':
                self._dispatch(cache)
                cache.clear()
                self._queue_constraint(tok.value)
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

    def _queue_constraint(self, annotation):
        constraint = annotation.split('@:')[1].strip()
        assert self._constraints is not None, \
            f'Constraint {constraint} can only be defined within a .SUBCKT \nCurrent scope:{self._scope[-1]}'
        self._constraints.append(constraint)

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
            if not kwargs:
                kwargs['VALUE'] = args.pop()
            else:  # to allow cap/res parameters
                model = args.pop()
        elif any(name.startswith(x) for x in ('M', 'X')):
            assert args, f"empty arguments found {name} {args} {kwargs}"
            model = args.pop()
        else:
            raise NotImplementedError(name, args, kwargs, "is not yet recognized by parser")

        if self.library.find(model):
            model = self.library.find(model)

            if model.base:
                generator = model.base
            elif isinstance(model, SubCircuit) and name.startswith('X'):
                generator = model.name
            elif isinstance(model, Model) and model.prefix == 'XI':
                generator = 'generic'
            else:
                generator = model.name
            # TODO assert generator is available in primitive generator
        else:
            # TODO generic model need to get pins from generator
            logger.info(f"unknown device found {model}, creating a generic model for this")
            with set_context(self.library):
                self.library.append(
                    Model(name=model, pins=args, parameters=kwargs, prefix='XI')
                )
            model = self.library.find(model)
            # TODO: get it from generator
            generator = 'generic'

        assert model is not None, (model, name, args, kwargs)
        assert len(args) == len(model.pins), \
            f"Model {model.name} has {len(model.pins)} pins {model.pins}. " \
            + f"{len(args)} nets {args} were passed when instantiating {name}."
        pins = {pin: net for pin, net in zip(model.pins, args)}
        with set_context(self._scope[-1].elements):
            try:
                self._scope[-1].elements.append(Instance(name=name, model=model.name,
                                                         pins=pins, parameters=kwargs,
                                                         generator=generator
                                                         ))
            except ValueError:
                assert False, f"could not identify device parameters {name} {kwargs} allowed parameters are {model.name} {model.parameters}"

    def _process_constraints(self):
        with set_context(self._scope[-1].constraints):
            for const in self._constraints:
                self._scope[-1].constraints.append(eval(const, {}, constraint_dict))
        self._constraints = None

    def _process_declaration(self, decl, args, kwargs):
        if decl == '.SUBCKT':
            self._constraints = []
            name = args.pop(0)
            assert not isinstance(self.library.find(name), SubCircuit), f"User is attempting to redeclare subcircuit {name}"
            with set_context(self.library):
                subckt = SubCircuit(name=name, pins=args, parameters=kwargs)
            self.library.append(subckt)
            self._scope.append(subckt)
        elif decl == '.ENDS':
            self._process_constraints()
            self._scope.pop()
        elif decl == '.PARAM':
            assert len(args) == 0, f"unsupported arguments {args}, probably missing default values"
            self._scope[-1].parameters.update({
                k.upper(): str(v).upper() for k, v in kwargs.items()
            })
        elif decl == '.MODEL':
            assert len(args) == 2, args
            name, base = args[0], args[1]
            assert self.library.find(name) is None, f"User is attempting to redeclare {name}"
            assert self.library.find(base) is not None, f"Base model {base} not found for model {name}"
            with set_context(self.library):
                self.library.append(Model(name=name, base=base, parameters=kwargs))
