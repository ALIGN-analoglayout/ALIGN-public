import pydantic
import abc
import z3

from typing import List, Union, NamedTuple, Optional
from typing_extensions import Literal

class BBox(NamedTuple):
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
        return BBox(*z3.Ints(f'{block}_llx {block}_lly {block}_urx {block}_ury'))

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
            solver.append(constraints)
            super().check(solver)

class AlignVertical(ConstraintBase):
    blocks : List[str]
    alignment : Literal['left', 'center', 'right']

ConstraintType=Union[ \
        AlignHorizontal, AlignVertical]

class ConstraintDB(pydantic.BaseModel):
    constraints: List[ConstraintType] \
            = pydantic.Field(default_factory=list)

    _solver = pydantic.PrivateAttr(default_factory=z3.Solver)

    @pydantic.validate_arguments
    def append(self, constraint: ConstraintType):
        self.constraints.append(constraint)
        constraint.check(self._solver)