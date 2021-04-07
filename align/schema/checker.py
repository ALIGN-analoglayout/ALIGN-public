import collections
from . import types
import abc
import random
import string

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    z3 = None
    logger.warning("Could not import z3. ConstraintDB will not look for spec inconsistency.")

class AbstractChecker(abc.ABC):
    @abc.abstractmethod
    def append(self, constraint):
        pass

    @abc.abstractmethod
    def __init__(self, constraint):
        pass

class Z3Checker(AbstractChecker):

    def append(self, constraint):
        if self._validation:
            self._solver.append(*constraint.check())
            assert self._solver.check() == z3.sat

    def __init__(self):
        self._commits = collections.OrderedDict()
        self._validation = z3 is not None
        if self._validation:
            self._solver = z3.Solver()

    def _gen_commit_id(self, nchar=8):
        id_ = ''.join(random.choices(string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_commit_id(nchar) if id_ in self._commits else id_

    def checkpoint(self):
        self._commits[self._gen_commit_id()] = len(self)
        if self._validation:
            self._solver.push()
        return next(reversed(self._commits))

    def _revert(self):
        if self._validation:
            self._solver.pop()
        _, length = self._commits.popitem()
        del self[length:]

    def revert(self, name=None):
        assert len(self._commits) > 0, 'Top of scope. Nothing to revert'
        if name is None or name == next(reversed(self._commits)):
            self._revert()
        else:
            assert name in self._commits
            self._revert()
            self.revert(name)

    @classmethod
    def GenerateVar(cls, name, **fields):
        if fields:
            return collections.namedtuple(
                name,
                fields.keys(),
            )(*z3.Ints(' '.join(fields.values())))
        else:
            return z3.Int(name)
