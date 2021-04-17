import abc
import more_itertools as itertools
import re

from . import types
from .types import Union, Optional, Literal, List
from .checker import Z3Checker

import logging
logger = logging.getLogger(__name__)

pattern = re.compile(r'(?<!^)(?=[A-Z])')


class SoftConstraint(types.BaseModel):

    constraint: str

    def __init__(self, *args, **kwargs):
        if 'constraint' not in kwargs:
            kwargs['constraint'] = pattern.sub(
                '_', self.__class__.__name__).lower()
        super().__init__(*args, **kwargs)


class HardConstraint(SoftConstraint, abc.ABC):

    @abc.abstractmethod
    def check(self, checker):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from HardConstraint
          MUST implement this function. Please check
          minimum number of arguments at the very least
        '''
        pass


class PlacementConstraint(HardConstraint):

    @abc.abstractmethod
    def check(self, checker):
        '''
        Initialize empty constraint list &
        return list of z3 constraints associated
        each bbox at least
        '''
        assert len(self.instances) >= 1


class Order(PlacementConstraint):
    '''
    All `instances` will be ordered along `direction`

    WARNING: `Order` does not imply aligment / overlap
    of any sort (See `Align`)

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
    instances: List[str]
    direction: Optional[Literal[
        'horizontal', 'vertical',
        'left_to_right', 'right_to_left',
        'bottom_to_top', 'top_to_bottom'
    ]]
    abut: Optional[bool] = False

    def check(self, checker):
        assert len(self.instances) >= 2

        def cc(b1, b2, c='x'):  # Create coordinate constraint
            if self.abut:
                return getattr(b1, f'ur{c}') == getattr(b2, f'll{c}')
            else:
                return getattr(b1, f'ur{c}') <= getattr(b2, f'll{c}')
        super().check(checker)
        bvars = checker.iter_bbox_vars(self.instances)
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
    `instances` will be aligned along `line`. Could be
    strict or relaxed depending on value of `line`

    WARNING: `Align` does not imply ordering of any sort
    (See `Order`)

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
    instances: List[str]
    line: Optional[Literal[
        'h_any', 'h_top', 'h_bottom', 'h_center',
        'v_any', 'v_left', 'v_right', 'v_center'
    ]]

    def check(self, checker):
        super().check(checker)
        assert len(self.instances) >= 2
        bvars = checker.iter_bbox_vars(self.instances)
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
                    checker.Or(  # We don't know which bbox is higher yet
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
                    checker.Or(  # We don't know which bbox is wider yet
                        checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx)
                    )
                )
            else:
                checker.append(
                    checker.Or(  # h_any OR v_any
                        checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                        checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx),
                        checker.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                        checker.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                    )
                )


class Enclose(HardConstraint):
    ''' 
    Enclose `instances` within a flexible bounding box
    with `min_` & `max_` bounds

    Note: Specifying any one of the following variables
    makes it a valid constraint but you may wish to 
    specify more than one for practical purposes

    > `min_height`
    > `max_height`

    > `min_width`
    > `max_width`

    > `min_aspect_ratio`
    > `max_aspect_ratio`
    '''
    instances: List[str]
    min_height: Optional[int]
    max_height: Optional[int]
    min_width: Optional[int]
    max_width: Optional[int]
    min_aspect_ratio: Optional[float]
    max_aspect_ratio: Optional[float]

    @types.root_validator(allow_reuse=True)
    def bound_in_box_optional_fields(cls, values):
        assert any(
            getattr(values, x)
            for x in (
                'min_height',
                'max_height',
                'min_width',
                'max_width',
                'min_aspect_ratio',
                'max_aspect_ratio'
            )
        )

    def check(self, checker):
        super().check(checker)
        assert len(self.instances) >= 2
        bb = checker.bbox_vars(id(self))
        if self.min_width:
            checker.append(
                bb.urx - bb.llx >= self.min_width
            )
        if self.min_height:
            checker.append(
                bb.ury - bb.lly >= self.min_height
            )
        if self.max_width:
            checker.append(
                bb.urx - bb.llx <= self.max_width
            )
        if self.max_height:
            checker.append(
                bb.ury - bb.lly <= self.max_height
            )
        if self.min_aspect_ratio:
            checker.append(
                checker.cast(
                    (bb.ury - bb.lly) / (bb.urx - bb.llx),
                    float) >= self.min_aspect_ratio
            )
        if self.max_aspect_ratio:
            checker.append(
                checker.cast(
                    (bb.ury - bb.lly) / (bb.urx - bb.llx),
                    float) <= self.max_aspect_ratio
            )
        bvars = checker.iter_bbox_vars(self.instances)
        for b in bvars:
            checker.append(b.urx <= bb.urx)
            checker.append(b.llx >= bb.llx)
            checker.append(b.ury <= bb.ury)
            checker.append(b.lly >= bb.lly)


class Spread(PlacementConstraint):
    '''
    Spread `instances` by forcing minimum spacing along 
    `direction` if two blocks overlap in other direction

    WARNING: This constraint checks for overlap but
    doesn't enforce it (See `Align`)

    The following `direction` values are supported:
    > `None` : default (`'horizontal'` or `'vertical'`)

    > `'horizontal'`
    > `'vertical'`
    '''

    instances: List[str]
    direction: Optional[Literal['horizontal', 'vertical']]
    distance: int  # in nm

    def check(self, checker):
        def cc(b1, b2, c='x'):
            d = 'y' if c == 'x' else 'x'
            return checker.Implies(
                checker.And(  # overlap orthogonal to c
                    getattr(b1, f'ur{d}') > getattr(b2, f'll{d}'),
                    getattr(b2, f'ur{d}') > getattr(b1, f'll{d}'),
                ),
                checker.Abs(  # distance in c coords
                    (
                        getattr(b1, f'll{c}')
                        + getattr(b1, f'ur{c}')
                    ) - (
                        getattr(b2, f'll{c}')
                        + getattr(b2, f'ur{c}')
                    )
                ) >= self.distance * 2
            )
        super().check(checker)
        assert len(self.instances) >= 2
        bvars = checker.iter_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.direction == 'horizontal':
                checker.append(
                    cc(b1, b2, 'x')
                )
            elif self.direction == 'vertical':
                checker.append(
                    cc(b1, b2, 'y')
                )
            else:
                checker.append(
                    checker.Or(
                        cc(b1, b2, 'x'),
                        cc(b1, b2, 'y')
                    )
                )


# You may chain constraints together for more complex constraints by
#     1) Assigning default values to certain attributes
#     2) Using custom validators to modify attribute values
# Note: Compositional check() is automatically constructed if
#     every check() in mro starts with `constraints = super().check()`.
#     (mro is Order, Align, HardConstraint in this example)
# Note: If you need to specialize check(), you do have the option
#     to create a custom `check()` in this class. It shouldn't be
#     needed unless you are adding new semantics


class AlignInOrder(Order, Align):
    '''
    Align `instances` on `line` ordered along `direction`

    Note: This is a user-convenience constraint. Same
    effect can be realized using `Order` & `Align`

    > `direction == 'horizontal'` => left_to_right

    > `direction == 'vertical'`   => bottom_to_top
    '''
    instances: List[str]
    direction: Optional[Literal['horizontal', 'vertical']]
    line: Optional[Literal[
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


class PlaceSymmetric(PlacementConstraint):
    # TODO: Finish implementing this. Not registered to
    #       ConstraintDB yet
    ''' 
    Place instance / pair of `instances` symmetrically 
    around line of symmetry along `direction`

    Note: This is a user-convenience constraint. Same
    effect can be realized using `Align` & `Group`

    For example:
    `instances` = [['1'], ['4', '5'], ['2', '3'], ['6']],
    `direction` = 'vertical'
       1   |  5 4  |   6   |  4 5  |   1   |  5 4
      4 5  |   1   |  5 4  |   6   |   6   |   1
      2 3  |  2 3  |  3 2  |   1   |  5 4  |   6
       6   |   6   |   1   |  2 3  |  2 3  |  3 2
    '''
    instances: List[List[str]]
    direction: Optional[Literal['horizontal', 'vertical']]

    def check(self, checker):
        '''
        X = Align(2, 3, 'h_center')
        Y = Align(4, 5, 'h_center')
        Align(1, X, Y, 6, 'center')

        '''
        assert len(self.instances) >= 1
        assert all(isinstance(x, List) for x in self.instances)


class OrderBlocks(SoftConstraint):
    '''
    TODO: Replace this with just Order
    '''
    instances: List[str]
    direction: Optional[Literal['H', 'V']]


class MatchBlocks(SoftConstraint):
    '''
    TODO: Can be replicated by Enclose??
    '''
    instances: List[str]

class SymmetricBlocks(SoftConstraint):
    instances: List[List[str]]
    direction: Optional[Literal['horizontal', 'vertical']]

class BlockDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    direction: None = None
    distance: int


class VerticalDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    direction: Literal['vertical'] = 'vertical'
    distance: int


class HorizontalDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    direction: Literal['horizontal'] = 'horizontal'
    distance: int


class AspectRatio(SoftConstraint):
    '''
    TODO: Replace with Enclose
    '''
    ratio_low: Optional[float]
    ratio_high: Optional[float]

    @types.root_validator(allow_reuse=True)
    def cast_aspect_ratio_spec(cls, values):
        if not values['ratio_low'] and not values['ratio_high']:
            raise AssertionError('At least one parameter must be specified')
        elif values['ratio_low']:
            values['ratio_high'] = 1 / values['ratio_low']
        else:
            values['ratio_low'] = 1 / values['ratio_high']
        return values


class GroupBlocks(SoftConstraint):
    ''' Force heirarchy creation '''
    name: str  # subcircuit name
    instances: List[str]


class GroupCaps(SoftConstraint):
    ''' Common Centroid Cap '''
    name: str  # subcircuit name
    instances: List[str]
    unit_cap: float  # cap value in fF
    dummy: bool  # whether to fill in dummies


class SymmetricNets(SoftConstraint):
    direction: Literal['H', 'V']
    net1: str
    net2: str
    pins1: List
    pins2: List


class MultiConnection(SoftConstraint):
    net: str
    multiplier: int


class ShieldNet(SoftConstraint):
    name: str
    shield: str


class CritNet(SoftConstraint):
    name: str
    criticality: int


class PortLocation(SoftConstraint):
    '''T (top), L (left), C (center), R (right), B (bottom)'''
    name: str
    location: Literal['TL', 'TC', 'TR',
                      'RT', 'RC', 'RB',
                      'BL', 'BC', 'BR',
                      'LB', 'LC', 'LT']


ConstraintType = Union[
    # ALIGN Internal DSL
    Order, Align,
    Enclose, Spread,
    # Additional helper constraints
    AlignInOrder,
    # Current Align constraints
    # Consider removing redundant ones
    OrderBlocks,
    MatchBlocks,
    SymmetricBlocks,
    BlockDistance,
    VerticalDistance,
    HorizontalDistance,
    AspectRatio,
    GroupBlocks,
    GroupCaps,
    SymmetricNets,
    MultiConnection,
    ShieldNet,
    CritNet,
    PortLocation
]


class ConstraintDB(types.List[ConstraintType]):

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr(None)

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        if self._checker:
            constraint.check(self._checker)
        super().append(constraint)

    def __init__(self):
        super().__init__(__root__=[])
        if Z3Checker.enabled:
            self._checker = Z3Checker()

    def checkpoint(self):
        if self._checker:
            self._checker.checkpoint()
        return super().checkpoint()

    def _revert(self):
        if self._checker:
            self._checker.revert()
        super()._revert()
