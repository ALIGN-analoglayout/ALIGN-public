import abc
import random
import string
import collections
import more_itertools as itertools

from . import types
from .types import Union, Optional, Literal, List

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    z3 = None
    logger.warning("Could not import z3. ConstraintDB will not look for spec inconsistency.")

class PlacementConstraint(types.BaseModel, abc.ABC):

    @abc.abstractmethod
    def check(self):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from PlacementConstraint
          MUST implement this function. Please check minimum
          number of arguments at the very least

        :return list of z3 constraints
        '''
        assert len(self.instances) >= 1
        constraints = []
        bvars = self._get_bbox_vars(self.instances)
        for b in bvars:
            constraints.append(b.llx < b.urx)
            constraints.append(b.lly < b.ury)
        return constraints

    @staticmethod
    def _get_bbox_vars(*instances):
        '''
        This function can be used in two ways:
        1) Get all bboxes for a list set of instances:
           (Useful for constraints that accept lists)
            l_bbox = self._z3_bbox_variables(instances)
        2) Choose which instances to get bbox vars for:
           (Useful for pairwise constraints)
            bbox1, bbox2 = self._z3_bbox_variables(box1, box2)
        '''
        if len(instances) == 1 and isinstance(instances[0], List):
            instances = instances[0]
        return [ConstraintDB.GenerateVar(
                    'Bbox',
                    llx = f'{instance}_llx',
                    lly = f'{instance}_lly',
                    urx = f'{instance}_urx',
                    ury = f'{instance}_ury') \
                for instance in instances]

class Order(PlacementConstraint):
    '''
    All `instances` will be ordered with respect to each other

    The following `direction` values are supported:
    > `None`

    > `'horizontal'`
    > `'vertical'`
    
    > `'left->right'`
    > `'right->left'`
    > `'bottom->top'`
    > `'top->bottom'`

    If `abut` is `True`:
    > adjoining instances will touch
    '''
    instances : List[str]
    direction: Optional[Literal[
        'horizontal', 'vertical',
        'left->right', 'right->left',
        'bottom->top', 'top->bottom'
    ]]
    abut: Optional[bool] = False

    def check(self):
        def cc(b1, b2, c='x'): # Create coordinate constraint
            if self.abut:
                return getattr(b1, f'ur{c}') == getattr(b2, f'll{c}')
            else:
                return getattr(b1, f'ur{c}') <= getattr(b2, f'll{c}')
        constraints = super().check()
        assert len(self.instances) >= 2
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.direction == 'left->right':
                constraints.append(cc(b1, b2, 'x'))
            elif self.direction == 'right->left':
                constraints.append(cc(b2, b1, 'x'))
            elif self.direction == 'bottom->top':
                constraints.append(cc(b1, b2, 'y'))
            elif self.direction == 'top->bottom':
                constraints.append(cc(b2, b1, 'y'))
            if self.direction == 'horizontal':
                constraints.append(
                    z3.Or(
                        cc(b1, b2, 'x'),
                        cc(b2, b1, 'x')))
            elif self.direction == 'vertical':
                constraints.append(
                    z3.Or(
                        cc(b1, b2, 'y'),
                        cc(b2, b1, 'y')))
            else:
                constraints.append(
                    z3.Or(
                        cc(b1, b2, 'x'),
                        cc(b2, b1, 'x'),
                        cc(b1, b2, 'y'),
                        cc(b2, b1, 'y')))

        return constraints

class Align(PlacementConstraint):
    '''
    All `instances` will be aligned along the specified `line`

    The following `line` values are currently supported:
    > `'top'`
    > `'bottom'`
    > `'middle'`
    
    > `'left'`
    > `'right'`
    > `'center'`

    '''
    instances : List[str]
    line : Literal[
        'top', 'bottom', 'middle',
        'left', 'right', 'center'
    ]

    def check(self):
        constraints = super().check()
        assert len(self.instances) >= 2
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'top':
                constraints.append(b1.ury == b2.ury)
            elif self.line == 'bottom':
                constraints.append(b1.lly == b2.lly)
            elif self.line == 'left':
                constraints.append(b1.llx == b2.llx)
            elif self.line == 'right':
                constraints.append(b1.urx == b2.urx)
            elif self.line == 'middle':
                constraints.append(
                    (b1.lly + b1.ury) / 2 == (b2.lly + b2.ury) / 2)
            elif self.line == 'center':
                constraints.append(
                    (b1.llx + b1.urx) / 2 == (b2.llx + b2.urx) / 2)
        return constraints

# TODO: Write a helper utility that allows custom
#       constraints to be added to ConstraintDB
#       Sample complex constraint below
# NOTE: This may even happen automatically if we
#       use List from .types as baseclass for
#       ConstraintDB

class AlignHorizontal(Order, Align):
    '''
    Chain simple constraints together for more complex constraints by
        assigning default values to certain attributes
    
    Note: Compositional check() is automatically constructed if
        every check() in mro starts with `constraints = super().check()`.
        (mro is Order, Align, ConstraintBase in this example)
    Note: If you need to specialize check(), you do have the option 
        to create a custom `check()` in this class. It shouldn't be
        needed unless you are adding new semantics
    '''
    instances : List[str]
    line : Optional[Literal['top', 'bottom']]
    direction: Literal['horizontal', 'left->right', 'right->left'] = 'left->right'
    abut: Optional[bool] = False

ConstraintType=Union[Order, Align, AlignHorizontal]

class ConstraintDB(types.BaseModel):

    __root__ : List[ConstraintType]

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        self.__root__.append(constraint)
        if self._validation:
            self._solver.append(*constraint.check())
            assert self._solver.check() == z3.sat

    def __init__(self, validation=None):
        super().__init__(__root__=[])
        self._commits = collections.OrderedDict()
        if z3 is not None:
            self._solver = z3.Solver()
            if validation is not None:
                self._validation = validation
        else:
            assert not validation, "Cannot validate without z3"

    #
    # Private attribute affecting class behavior
    #
    _solver = types.PrivateAttr()
    _commits = types.PrivateAttr()
    _validation = types.PrivateAttr(default_factory=lambda: z3 is not None)

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
        self._commits[self._gen_commit_id()] = len(self.__root__)
        if self._validation:
            self._solver.push()
        return next(reversed(self._commits))

    def _revert(self):
        if self._validation:
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
