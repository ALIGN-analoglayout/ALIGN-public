import pydantic
import abc
import z3
import random
import string
import collections

from typing import List, Union, NamedTuple, Optional
from typing_extensions import Literal

class BBoxVars(NamedTuple):
    llx: z3.Int
    lly: z3.Int
    urx: z3.Int
    ury: z3.Int

class ConstraintBase(pydantic.BaseModel, abc.ABC):

    class Config:
        validate_assignment = True
        extra = 'forbid'

    @abc.abstractmethod
    def check(self, solver):
        assert solver.check() == z3.sat

    @staticmethod
    def _get_bbox_variables(block):
        return BBoxVars(*z3.Ints(f'{block}_llx {block}_lly {block}_urx {block}_ury'))

class AlignHorizontal(ConstraintBase):
    '''
    All blocks in 'block' will be lined up (in order) on the X axis

    The optional 'alignment' parameter determines alignment along Y axis
    '''
    blocks : List[str]
    alignment : Optional[Literal['top', 'middle', 'bottom']] = 'middle'

    def check(self, solver=None):
        constraints = []
        blocks = iter(self.blocks)
        block1 = next(blocks, None)
        assert block1, f'{self.__class__.__name__} must contain at least two blocks'
        b1 = self._get_bbox_variables(block1)
        constraints.append(b1.llx < b1.urx)
        block2 = next(blocks, None)
        assert block2, f'{self.__class__.__name__} must contain at least two blocks'
        while(block1 and block2):
            b1 = self._get_bbox_variables(block1)
            b2 = self._get_bbox_variables(block2)
            constraints.append(b1.urx <= b2.llx)
            constraints.append(b2.llx < b2.urx)
            block1 = block2
            block2 = next(blocks, None)
        if solver:
            solver.append(*constraints)
            super().check(solver)

class AlignVertical(ConstraintBase):
    blocks : List[str]
    alignment : Literal['left', 'center', 'right']

ConstraintType=Union[ \
        AlignHorizontal, AlignVertical]

class ConstraintDB():

    @property
    def constraints(self):
        return tuple(self._constraints)

    @pydantic.validate_arguments
    def append(self, constraint: ConstraintType):
        self._constraints.append(constraint)
        constraint.check(self._solver)

    def __init__(self):
        self._constraints = []
        self._solver = z3.Solver()
        self._commits = collections.OrderedDict()

    def _gen_commit_id(self, nchar=8):
        id_ = ''.join(random.choices(string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_commit_id(nchar) if id_ in self._commits else id_

    def checkpoint(self):
        self._solver.push()
        self._commits[self._gen_commit_id()] = len(self._constraints)
        assert len(self._commits) == self._solver.num_scopes()
        return next(reversed(self._commits))

    def _revert(self):
        self._solver.pop()
        _, length = self._commits.popitem()
        assert len(self._commits) == self._solver.num_scopes()
        self._constraints = self._constraints[0:length-1]

    def revert(self, name=None):
        assert len(self._commits) > 0, 'Top of scope. Nothing to revert'
        if name is None or name == next(reversed(self._commits)):
            self._revert()
        else:
            assert name in self._commits
            self._revert()
            self.revert(name)
