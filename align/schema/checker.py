import abc
import collections

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    logger.warning("Could not import z3. Z3Checker disabled.")
    z3 = None

class AbstractChecker(abc.ABC):
    @abc.abstractmethod
    def append(self, formula):
        '''
        Append formula to checker.

        Note: Please use bbox variables to create formulae
              Otherwise you will need to manage types
              yourself
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
    def bbox(self, *instances):
        '''
        Helper utility to generate bbox variables

        This function can be used in two ways:
        1) Get all bboxes for a list set of instances:
           (Useful for constraints that accept lists)
            l_bbox = self._z3_bbox_variables(instances)
        2) Choose which instances to get bbox vars for:
           (Useful for pairwise constraints)
            bbox1, bbox2 = self._z3_bbox_variables(box1, box2)
        '''
        pass

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
    def Or(self, *expressions):
        '''
        Logical `Not` of all arguments

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

    @property
    @abc.abstractmethod
    def enabled(self):
        pass

class Z3Checker(AbstractChecker):

    enabled = z3 is not None

    def __init__(self):
        self._solver = z3.Solver()

    def append(self, formula):
        self._solver.append(formula)
        assert self._solver.check() == z3.sat

    def checkpoint(self):
        self._solver.push()

    def revert(self):
        self._solver.pop()

    @staticmethod
    def bbox(*instances):
        if len(instances) == 1 and not hasattr(instances[0], 'check'):
            instances = instances[0]
        return [Z3Checker._generate_var(
                    'Bbox',
                    llx = f'{instance}_llx',
                    lly = f'{instance}_lly',
                    urx = f'{instance}_urx',
                    ury = f'{instance}_ury') \
                for instance in instances]

    @staticmethod
    def Or(*expressions):
        return z3.Or(*expressions)

    @staticmethod
    def And(*expressions):
        return z3.And(*expressions)

    @staticmethod
    def Implies(expr1, expr2):
        return z3.Implies(expr1, expr2)

    @staticmethod
    def _generate_var(name, **fields):
        if fields:
            return collections.namedtuple(
                name,
                fields.keys(),
            )(*z3.Ints(' '.join(fields.values())))
        else:
            return z3.Int(name)
