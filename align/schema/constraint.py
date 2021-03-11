import abc
import z3
import random
import string
import collections
import more_itertools as itertools

from . import schema
from .types import Union, NamedTuple, Optional, Literal, List, PrivateAttr

class ConstraintBase(schema.BaseModel, abc.ABC):

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
        bvars = self._get_bbox_vars(self.blocks)
        for b in bvars:
            constraints.append(b.llx < b.urx)
            constraints.append(b.lly < b.ury)
        return constraints

    @staticmethod
    def _get_bbox_vars(*blocks):
        '''
        This function can be used in two ways:
        1) Get all bboxes for a list set of blocks:
           (Useful for constraints that accept lists)
            l_bbox = self._z3_bbox_variables(blocks)
        2) Choose which blocks to get bbox vars for:
           (Useful for pairwise constraints)
            bbox1, bbox2 = self._z3_bbox_variables(box1, box2)
        '''
        print([block for block in blocks])
        if len(blocks) == 1 and isinstance(blocks[0], List):
            blocks = blocks[0]
        return [ConstraintDB.GenerateVar(
                    'Bbox',
                    llx = f'{block}_llx',
                    lly = f'{block}_lly',
                    urx = f'{block}_urx',
                    ury = f'{block}_ury') \
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
        bvars = self._get_bbox_vars(self.blocks)
        for b1, b2 in itertools.pairwise(bvars):
            constraints.append(b1.urx <= b2.llx)
        return constraints

class AlignVertical(ConstraintBase):
    blocks : List[str]
    alignment : Literal['left', 'center', 'right']

ConstraintType=Union[ \
        AlignHorizontal, AlignVertical]

class ConstraintDB(schema.BaseModel):

    __root__ : List[ConstraintType]

    @schema.validate_arguments
    def append(self, constraint: ConstraintType):
        self.__root__.append(constraint)
        if self._validation:
            self._solver.append(*constraint.check())
            assert self._solver.check() == z3.sat

    def __init__(self, validation=True):
        super().__init__(__root__=[])
        self._solver = z3.Solver()
        self._commits = collections.OrderedDict()
        self._validation = validation

    #
    # Private attribute affecting class behavior
    #
    _solver = PrivateAttr()
    _commits = PrivateAttr()
    _validation = PrivateAttr()

    def __iter__(self):
        return iter(self.__root__)

    def __getitem__(self, item):
        return self.__root__[item]

    def __len__(self):
        return len(self.__root__)

    def _gen_commit_id(self, nchar=8):
        id_ = ''.join(random.choices(string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_commit_id(nchar) if id_ in self._commits else id_

    def checkpoint(self):
        self._solver.push()
        self._commits[self._gen_commit_id()] = len(self.__root__)
        return next(reversed(self._commits))

    def _revert(self):
        self._solver.pop()
        _, length = self._commits.popitem()
        del self.__root__[length:]

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