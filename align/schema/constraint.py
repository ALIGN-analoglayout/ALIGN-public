import abc
import random
import string
import collections
import more_itertools as itertools
import re

from . import types
from .types import Union, Optional, Literal, List

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    z3 = None
    logger.warning("Could not import z3. ConstraintDB will not look for spec inconsistency.")

pattern = re.compile(r'(?<!^)(?=[A-Z])')
class ConstraintBase(types.BaseModel, abc.ABC):

    constraint : str

    def __init__(self, *args, **kwargs):
        if 'constraint' not in kwargs:
            kwargs['constraint'] = pattern.sub('_', self.__class__.__name__).lower()
        super().__init__(*args, **kwargs)

    @abc.abstractmethod
    def check(self):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from ConstraintBase
          MUST implement this function. Please check minimum
          number of arguments at the very least
        '''
        return []

class PlacementConstraint(ConstraintBase):

    @abc.abstractmethod
    def check(self):
        '''
        Initialize empty constraint list &
        return list of z3 constraints associated
        each bbox at least
        '''
        constraints = super().check()
        assert len(self.instances) >= 1
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
    > `None` : default (`'horizontal'` or `'vertical'`)

    > `'horizontal'`: left to right or vice-versa

    > `'vertical'`: bottom to top or vice-versa
    
    > `'left_to_right'`
    > `'right_to_left'`
    > `'bottom_to_top'`
    > `'top_to_bottom'`

    If `abut` is `True`:
    > adjoining instances will touch
    '''
    instances : List[str]
    direction: Optional[Literal[
        'horizontal', 'vertical',
        'left_to_right', 'right_to_left',
        'bottom_to_top', 'top_to_bottom'
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
            if self.direction == 'left_to_right':
                constraints.append(cc(b1, b2, 'x'))
            elif self.direction == 'right_to_left':
                constraints.append(cc(b2, b1, 'x'))
            elif self.direction == 'bottom_to_top':
                constraints.append(cc(b1, b2, 'y'))
            elif self.direction == 'top_to_bottom':
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
    > `None` : default (`'h_any'` or `'v_any'`)

    > `'h_any'`: top, bottom or anything in between

    > `'v_any'`: left, right or anything in between
    
    > `'h_top'`
    > `'h_bottom'`
    > `'h_center'`
    
    > `'v_left'`
    > `'v_right'`
    > `'v_center'`
    '''
    instances : List[str]
    line : Optional[Literal[
        'h_any', 'h_top', 'h_bottom', 'h_center',
        'v_any', 'v_left', 'v_right', 'v_center'
    ]]

    def check(self):
        constraints = super().check()
        assert len(self.instances) >= 2
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'h_top':
                constraints.append(b1.ury == b2.ury)
            elif self.line == 'h_bottom':
                constraints.append(b1.lly == b2.lly)
            elif self.line == 'h_center':
                constraints.append(
                    (b1.lly + b1.ury) / 2 == (b2.lly + b2.ury) / 2)
            elif self.line == 'h_any':
                constraints.append(
                    z3.Or( # We don't know which bbox is higher yet
                        z3.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                        z3.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                    )
                )
            elif self.line == 'v_left':
                constraints.append(b1.llx == b2.llx)
            elif self.line == 'v_right':
                constraints.append(b1.urx == b2.urx)
            elif self.line == 'v_center':
                constraints.append(
                    (b1.llx + b1.urx) / 2 == (b2.llx + b2.urx) / 2)
            elif self.line == 'v_any':
                constraints.append(
                    z3.Or( # We don't know which bbox is wider yet
                        z3.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        z3.And(b2.urx <= b1.urx, b2.llx >= b1.llx)
                    )
                )
            else:
                constraints.append(
                    z3.Or( # h_any OR v_any
                        z3.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        z3.And(b2.urx <= b1.urx, b2.llx >= b1.llx),
                        z3.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                        z3.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                    )
                )
        return constraints

# You may chain constraints together for more complex constraints by
#     1) Assigning default values to certain attributes
#     2) Using custom validators to modify attribute values
# Note: Compositional check() is automatically constructed if
#     every check() in mro starts with `constraints = super().check()`.
#     (mro is Order, Align, ConstraintBase in this example)
# Note: If you need to specialize check(), you do have the option 
#     to create a custom `check()` in this class. It shouldn't be
#     needed unless you are adding new semantics
class AlignInOrder(Order, Align):
    '''
    Align `instances` in order, along the `direction`, on the `line`

    > `direction == 'horizontal'` => left_to_right

    > `direction == 'vertical'`   => bottom_to_top
    '''
    instances : List[str]
    direction: Optional[Literal['horizontal', 'vertical']]
    line : Optional[Literal[
        'top', 'bottom',
        'left', 'right',
        'center'
    ]]
    abut: Optional[bool] = False

    @types.root_validator(allow_reuse=True)
    def _cast_constraints_to_base_types(cls, values):
        # Process unambiguous line values
        if values['line'] in ['bottom', 'top']:
            if values['direction'] is None:
                values['direction'] = 'horizontal'
            else:
                assert values['direction'] == 'horizontal', \
                    f'direction is horizontal if line is bottom or top'
            values['line'] = f"h_{values['line']}"
        elif values['line'] in ['left', 'right']:
            if values['direction'] is None:
                values['direction'] = 'vertical'
            else:
                assert values['direction'] == 'vertical', \
                    f'direction is vertical if line is left or right'
            values['line'] = f"v_{values['line']}"
        # Center needs both line & direction
        elif values['line'] == 'center':
            assert values['direction'], \
                'direction must be specified if line == center'
            values['line'] = f"{values['direction'][0]}_{values['line']}"
        # Map horizontal, vertical direction to left_to_right & bottom_to_top
        if values['direction'] == 'horizontal':
            values['direction'] = 'left_to_right'
        elif values['direction'] == 'vertical':
            values['direction'] = 'bottom_to_top'
        return values

ConstraintType=Union[Order, Align, AlignInOrder]

class ConstraintDB(types.List[ConstraintType]):

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        super().append(constraint)
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
