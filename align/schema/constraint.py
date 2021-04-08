import abc
import more_itertools as itertools
import re

from . import types
from .types import Union, Optional, Literal, List
from .checker import Z3Checker

import logging
logger = logging.getLogger(__name__)

pattern = re.compile(r'(?<!^)(?=[A-Z])')
class ConstraintBase(types.BaseModel, abc.ABC):

    constraint : str

    def __init__(self, *args, **kwargs):
        if 'constraint' not in kwargs:
            kwargs['constraint'] = pattern.sub('_', self.__class__.__name__).lower()
        super().__init__(*args, **kwargs)

    @abc.abstractmethod
    def check(self, checker):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from ConstraintBase
          MUST implement this function. Please check minimum
          number of arguments at the very least
        '''
        pass

class PlacementConstraint(ConstraintBase):

    @abc.abstractmethod
    def check(self, checker):
        '''
        Initialize empty constraint list &
        return list of z3 constraints associated
        each bbox at least
        '''
        assert len(self.instances) >= 1
        bvars = checker.bbox(self.instances)
        for b in bvars:
            checker.append(b.llx < b.urx)
            checker.append(b.lly < b.ury)

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

    def check(self, checker):
        assert len(self.instances) >= 2
        def cc(b1, b2, c='x'): # Create coordinate constraint
            if self.abut:
                return getattr(b1, f'ur{c}') == getattr(b2, f'll{c}')
            else:
                return getattr(b1, f'ur{c}') <= getattr(b2, f'll{c}')
        super().check(checker)
        bvars = checker.bbox(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.direction == 'left_to_right':
                checker.append(cc(b1, b2, 'x'))
            elif self.direction == 'right_to_left':
                checker.append(cc(b2, b1, 'x'))
            elif self.direction == 'bottom_to_top':
                checker.append(cc(b1, b2, 'y'))
            elif self.direction == 'top_to_bottom':
                checker.append(cc(b2, b1, 'y'))
            if self.direction == 'horizontal':
                checker.append(
                    checker.Or(
                        cc(b1, b2, 'x'),
                        cc(b2, b1, 'x')))
            elif self.direction == 'vertical':
                checker.append(
                    checker.Or(
                        cc(b1, b2, 'y'),
                        cc(b2, b1, 'y')))
            else:
                checker.append(
                    checker.Or(
                        cc(b1, b2, 'x'),
                        cc(b2, b1, 'x'),
                        cc(b1, b2, 'y'),
                        cc(b2, b1, 'y')))

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

    def check(self, checker):
        super().check(checker)
        assert len(self.instances) >= 2
        bvars = checker.bbox(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'h_top':
                checker.append(b1.ury == b2.ury)
            elif self.line == 'h_bottom':
                checker.append(b1.lly == b2.lly)
            elif self.line == 'h_center':
                checker.append(
                    (b1.lly + b1.ury) / 2 == (b2.lly + b2.ury) / 2)
            elif self.line == 'h_any':
                checker.append(
                    checker.Or( # We don't know which bbox is higher yet
                        checker.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                        checker.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                    )
                )
            elif self.line == 'v_left':
                checker.append(b1.llx == b2.llx)
            elif self.line == 'v_right':
                checker.append(b1.urx == b2.urx)
            elif self.line == 'v_center':
                checker.append(
                    (b1.llx + b1.urx) / 2 == (b2.llx + b2.urx) / 2)
            elif self.line == 'v_any':
                checker.append(
                    checker.Or( # We don't know which bbox is wider yet
                        checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx)
                    )
                )
            else:
                checker.append(
                    checker.Or( # h_any OR v_any
                        checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx),
                        checker.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                        checker.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                    )
                )

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

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr()

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        constraint.check(self._checker)
        super().append(constraint)

    def __init__(self):
        super().__init__(__root__=[])
        self._checker = Z3Checker()
        if not self._checker.enabled:
            self._checker = None

    def checkpoint(self):
        if self._checker:
            self._checker.checkpoint()
        return super().checkpoint()

    def _revert(self):
        if self._checker:
            self._checker.revert()
        super()._revert()