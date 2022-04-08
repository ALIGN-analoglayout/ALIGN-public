import z3
import abc
import collections

import logging
logger = logging.getLogger(__name__)

class SolutionNotFoundError(Exception):
    def __init__(self, message, labels=None):
        self.message = message
        self.labels = labels
        super().__init__(self.message)


class AbstractSolver(abc.ABC):
    @abc.abstractmethod
    def append(self, formula, label=None):
        '''
        Append formula to checker.

        Note: Please use bbox variables to create formulae
              Otherwise you will need to manage types
              yourself
        '''
        pass

    @abc.abstractmethod
    def solve(self):
        '''
        Solve & return solutions

        If no solution is found, raise SolutionNotFoundError
        '''
        pass

    @abc.abstractmethod
    def label(self, object):
        '''
        Generate label that can be used for 
        back-annotation

        Note: Return None if solver
              doesn't support back-annotation
        '''
        pass

    @abc.abstractmethod
    def annotate(self, formulae, label):
        '''
        Yield formulae annotated with label      

        Note: Input 'formulae' is iterable.
        Note: MUST return an iterable object
        Note: Return original iterable if solver
              doesn't support back-annotation
        '''
        pass

    @abc.abstractmethod
    def checkpoint(self):
        '''
        Checkpoint current state of solver

        Note: We assume incremental solving here
              May need to revisit if we have to 
              rebuild solution from scratch
        '''
        pass

    @abc.abstractmethod
    def revert(self):
        '''
        Revert to last checkpoint

        Note: We assume incremental solving here
              May need to revisit if we have to 
              rebuild solution from scratch
        '''
        pass

    @abc.abstractmethod
    def bbox_vars(self, name):
        '''
        Generate a single namedtuple containing
        appropriate checker variables for
        placement constraints
        '''
        pass

    def iter_bbox_vars(self, names):
        '''
        Helper utility to generate multiple bbox variables

        The output should be an iterator that allows you
        to loop over bboxes (use `yield` when possible)
        '''
        for name in names:
            yield self.bbox_vars(name)

    @abc.abstractmethod
    def And(self, *expressions):
        '''
        Logical `And` of all arguments

        Note: arguments are assumed to be
              boolean expressions
        '''
        pass

    @abc.abstractmethod
    def Or(self, *expressions):
        '''
        Logical `Or` of all arguments

        Note: arguments are assumed to be
              boolean expressions
        '''
        pass

    @abc.abstractmethod
    def Not(self, expr):
        '''
        Logical `Not` of argument

        Note: argument is assumed to be
              a boolean expression
        '''
        pass

    @abc.abstractmethod
    def Implies(self, expr1, expr2):
        '''
        expr1 => expr2

        Note: both arguments are assumed
              to be boolean expressions
        '''
        pass

    @abc.abstractmethod
    def cast(expr, type_):
        '''
        cast `expr` to `type_`

        Note: Use with care. Not all 
              engines support all types
        '''
        pass

    @abc.abstractmethod
    def Abs(self, expr):
        '''
        Absolute value of expression

        Note: argument is assumed to be
              arithmetic expression
        '''
        pass

AnnotatedFormula = collections.namedtuple('AnnotatedFormula', ['formula', 'label'])

class Z3Checker(AbstractSolver):

    def __init__(self):
        self._solver = z3.Solver()
        self._solver.set(unsat_core=True)
        self._label_cache = set()

    def annotate(self, formulae, label):
        yield AnnotatedFormula(
        formula=self.And(
            *formulae
        ) if len(formulae) > 1 else formulae[0],
        label=label)

    def append(self, formula):
        if isinstance(formula, AnnotatedFormula):
            if formula.label not in self._label_cache:
                self._solver.assert_and_track(formula.formula, formula.label)
                self._label_cache.add(formula.label)
        else:
            self._solver.add(formula)

    def solve(self):
        r = self._solver.check()
        if r == z3.unsat:
            z3.set_option(max_depth=10000, max_args=100, max_lines=10000)
            logger.debug(f"Unsat encountered: {self._solver}")
            raise SolutionNotFoundError(
                message='No satisfying solution could be found. Please review constraints.',
                labels=self._solver.unsat_core())

    def checkpoint(self):
        self._solver.push()

    def revert(self):
        self._solver.pop()

    def bbox_vars(self, name):
        # generate new bbox
        return self._generate_var(
            'Bbox',
            llx=f'{name}_llx',
            lly=f'{name}_lly',
            urx=f'{name}_urx',
            ury=f'{name}_ury')

    def label(self, object):
        # Z3 throws 'index out of bounds' error
        # if more than 9 digits are used
        return z3.Bool(
            hash(repr(object)) % 10**9
        )

    @staticmethod
    def Or(*expressions):
        return z3.Or(*expressions)

    @staticmethod
    def And(*expressions):
        return z3.And(*expressions)

    @staticmethod
    def Not(expr):
        return z3.Not(expr)

    @staticmethod
    def Abs(expr):
        return z3.If(expr >= 0, expr, expr * -1)

    @staticmethod
    def Implies(expr1, expr2):
        return z3.Implies(expr1, expr2)

    @staticmethod
    def cast(expr, type_):
        if type_ == float:
            return z3.ToReal(expr)
        else:
            raise NotImplementedError

    @staticmethod
    def _generate_var(name, **fields):
        if fields:
            return collections.namedtuple(
                name,
                fields.keys(),
            )(*z3.Ints(' '.join(fields.values())))
        else:
            return z3.Int(name)
