import abc
import collections

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    logger.warning("Could not import z3. Z3Checker disabled.")
    z3 = None


class CheckerError(Exception):
    def __init__(self, message, labels=None):
        self.message = message
        self.labels = labels
        super().__init__(self.message)


class AbstractChecker(abc.ABC):
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
    def label(self, object):
        '''
        Generate label that can be used for 
        back-annotation
        '''
        return None

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


class Z3Checker(AbstractChecker):

    enabled = z3 is not None

    def __init__(self):
        self._label_cache = {}
        self._bbox_cache = {}
        self._bbox_subcircuit = {}
        self._solver = z3.Solver()
        self._solver.set(unsat_core=True)

    def append(self, formula, label=None):
        if label is not None:
            self._solver.assert_and_track(formula, label)
        else:
            self._solver.add(formula)
        r = self._solver.check()
        if r == z3.unsat:
            z3.set_option(max_depth=10000, max_args=100, max_lines=10000)
            logger.debug(f"Unsat encountered: {self._solver}")
            raise CheckerError(
                message=f'Trying to add {formula} resulted in unsat',
                labels=self._solver.unsat_core())

    def label(self, object):
        return z3.Bool(str(id(object)))

    def checkpoint(self):
        self._solver.push()

    def revert(self):
        self._solver.pop()

    def bbox_vars(self, name, is_subcircuit=False):
        # bbox was previously generated
        if name in self._bbox_cache:
            return self._bbox_cache[name]
        # generate new bbox
        b = self._generate_var(
            'Bbox',
            llx=f'{name}_llx',
            lly=f'{name}_lly',
            urx=f'{name}_urx',
            ury=f'{name}_ury')
        # width / height cannot be 0
        self.append(b.llx < b.urx)
        self.append(b.lly < b.ury)
        if is_subcircuit:
            self._bbox_subcircuit[name] = True
        else:
            # Do not overlap with other instance bboxes
            for k2, b2 in self._bbox_cache.items():
                if k2 not in self._bbox_subcircuit:
                    self.append(
                        self.Or(
                            b.urx <= b2.llx,
                            b2.urx <= b.llx,
                            b.ury <= b2.lly,
                            b2.ury <= b.lly,
                        )
                    )
        self._bbox_cache[name] = b
        return b

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
