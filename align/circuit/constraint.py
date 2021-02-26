import pydantic
import abc
import z3
import random
import string
import collections
import more_itertools as itertools

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
        allow_mutation = False

    @abc.abstractmethod
    def check(self):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from ConstraintBase
          MUST implement this function. Please check minimum
          number of arguments at the very least

        :return list of z3 constraints
        '''
        assert len(self.blocks) >= 1
        constraints = []
        bvars = self._get_z3_bbox_vars(self.blocks)
        for b in bvars:
            constraints.append(b.llx < b.urx)
            constraints.append(b.lly < b.ury)
        return constraints

    @staticmethod
    def _get_z3_bbox_vars(*blocks):
        '''
        This function can be used in two ways:
        1) Get all bboxes for a list set of blocks:
           (Useful for constraints that accept lists)
            l_bbox = self._z3_bbox_variables(blocks)
        2) Choose which blocks to get bbox vars for:
           (Useful for pairwise constraints)
            bbox1, bbox2 = self._z3_bbox_variables(box1, box2)
        '''
        if len(blocks) == 1 and isinstance(blocks[0], list):
            blocks = blocks[0]
        return [BBoxVars(*z3.Ints(f'{block}_llx {block}_lly {block}_urx {block}_ury')) \
                for block in blocks]

class AlignHorizontal(ConstraintBase):
    '''
    All blocks in 'block' will be lined up (in order) on the X axis

    The optional 'alignment' parameter determines alignment along Y axis
    '''
    blocks : List[str]
    alignment : Optional[Literal['top', 'middle', 'bottom']] = 'middle'

    def check(self):
        constraints = super().check()
        assert len(self.blocks) >= 2
        bvars = self._get_z3_bbox_vars(self.blocks)
        for b1, b2 in itertools.pairwise(bvars):
            constraints.append(b1.urx <= b2.llx)
        return constraints

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
        if self._validation:
            self._solver.append(*constraint.check())
            assert self._solver.check() == z3.sat

    def __init__(self, validation=True):
        self._constraints = []
        self._solver = z3.Solver()
        self._commits = collections.OrderedDict()
        self._validation = validation

    def _gen_commit_id(self, nchar=8):
        id_ = ''.join(random.choices(string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_commit_id(nchar) if id_ in self._commits else id_

    def checkpoint(self):
        self._solver.push()
        self._commits[self._gen_commit_id()] = len(self._constraints)
        return next(reversed(self._commits))

    def _revert(self):
        self._solver.pop()
        _, length = self._commits.popitem()
        self._constraints = self._constraints[0:length]

    def revert(self, name=None):
        assert len(self._commits) > 0, 'Top of scope. Nothing to revert'
        if name is None or name == next(reversed(self._commits)):
            self._revert()
        else:
            assert name in self._commits
            self._revert()
            self.revert(name)
