import abc
import more_itertools as itertools
import re

from . import types
from .types import Union, Optional, Literal, List
from . import checker

import logging
logger = logging.getLogger(__name__)

pattern = re.compile(r'(?<!^)(?=[A-Z])')


class SoftConstraint(types.BaseModel):

    constraint: str

    def __init__(self, *args, **kwargs):
        constraint = pattern.sub(
            '_', self.__class__.__name__).lower()
        if 'constraint' not in kwargs or kwargs['constraint'] == self.__class__.__name__:
            kwargs['constraint'] = constraint
        else:
            assert constraint == kwargs[
                'constraint'], f'Unexpected `constraint` {kwargs["constraint"]} (expected {constraint})'
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


class UserConstraint(SoftConstraint, abc.ABC):

    @abc.abstractmethod
    def yield_constraints(self):
        '''
        Abstract Method to yield low level constraints
          Every class that inherits from UserConstraint
          MUST implement this function. This ensures
          clean separation of user-facing constraints
          from PnR constraints
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


class Enclose(PlacementConstraint):
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
            getattr(values, x, None)
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
    `direction` if two instances overlap in other direction

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


class SetBoundingBox(HardConstraint):
    instance: str
    llx: int
    lly: int
    urx: int
    ury: int
    is_subcircuit: Optional[bool] = False

    def check(self, checker):
        super().check(checker)
        assert self.llx < self.urx and self.lly < self.ury, f'Reflection is not supported yet for {self}'
        bvar = checker.bbox_vars(self.instance, is_subcircuit=self.is_subcircuit)
        checker.append(bvar.llx == self.llx)
        checker.append(bvar.lly == self.lly)
        checker.append(bvar.urx == self.urx)
        checker.append(bvar.ury == self.ury)


# You may chain constraints together for more complex constraints by
#     1) Assigning default values to certain attributes
#     2) Using custom validators to modify attribute values
# Note: Compositional check() is automatically constructed if
#     every check() in mro starts with `constraints = super().check()`.
#     (mro is Order, Align, HardConstraint in this example)
# Note: If you need to specialize check(), you do have the option
#     to create a custom `check()` in this class. It shouldn't be
#     needed unless you are adding new semantics


class AlignInOrder(UserConstraint):
    '''
    Align `instances` on `line` ordered along `direction`

    Note: This is a user-convenience constraint. Same
    effect can be realized using `Order` & `Align`

    > `direction == 'horizontal'` => left_to_right

    > `direction == 'vertical'`   => bottom_to_top
    '''
    instances: List[str]
    line: Literal[
        'top', 'bottom',
        'left', 'right',
        'center'
    ] = 'bottom'
    direction: Optional[Literal['horizontal', 'vertical']]
    abut: Optional[bool] = False

    @types.validator('direction', allow_reuse=True, always=True)
    def _direction_depends_on_line(cls, v, values):
        # Process unambiguous line values
        if values['line'] in ['bottom', 'top']:
            if v is None:
                v = 'horizontal'
            else:
                assert v == 'horizontal', \
                    f'direction is horizontal if line is bottom or top'
        elif values['line'] in ['left', 'right']:
            if v is None:
                v = 'vertical'
            else:
                assert v == 'vertical', \
                    f'direction is vertical if line is left or right'
        # Center needs both line & direction
        elif values['line'] == 'center':
            assert v, \
                'direction must be specified if line == center'
        return v

    def yield_constraints(self):
        yield Align(
            instances=self.instances,
            line=f'{self.direction[0]}_{self.line}'
        )
        yield Order(
            instances=self.instances,
            direction='left_to_right' if self.direction == 'horizontal' else 'top_to_bottom',
            abut=self.abut
        )


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


class CreateAlias(SoftConstraint):
    instances: List[str]
    name: str


class GroupBlocks(SoftConstraint):
    ''' Force heirarchy creation '''
    name: str
    instances: List[str]
    style: Optional[Literal["tbd_interdigitated", "tbd_common_centroid"]]


class MatchBlocks(SoftConstraint):
    '''
    TODO: Can be replicated by Enclose??
    '''
    instances: List[str]


class SymmetricBlocks(SoftConstraint):
    pairs: List[List[str]]
    direction: Literal['H', 'V']


class BlockDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    abs_distance: int


class VerticalDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    abs_distance: int


class HorizontalDistance(SoftConstraint):
    '''
    TODO: Replace with Spread
    '''
    abs_distance: int

class GuardRing(SoftConstraint):
    '''
    Adds guard ring for particular hierarchy
    '''
    guard_ring_primitives: str
    global_pin: str
    block_name: str


class GroupCaps(SoftConstraint):
    ''' Common Centroid Cap '''
    name: str  # subcircuit name
    instances: List[str]
    unit_cap: str  # cap value in fF
    num_units: List
    dummy: bool  # whether to fill in dummies


class NetConst(SoftConstraint):
    nets: List[str]
    shield: str
    criticality: int


class PortLocation(SoftConstraint):
    '''T (top), L (left), C (center), R (right), B (bottom)'''
    ports: List
    location: Literal['TL', 'TC', 'TR',
                      'RT', 'RC', 'RB',
                      'BL', 'BC', 'BR',
                      'LB', 'LC', 'LT']


class SymmetricNets(SoftConstraint):
    net1: str
    net2: str
    pins1: Optional[List]
    pins2: Optional[List]
    direction: Literal['H', 'V']


class AspectRatio(HardConstraint):
    """
    Define lower and upper bounds on aspect ratio (=width/height) of a subcircuit

    `ratio_low` <= width/height <= `ratio_high`
    """
    subcircuit: str
    ratio_low: float = 0.1
    ratio_high: float = 10
    weight: int = 1

    def check(self, checker):
        assert self.ratio_low >= 0, f'AspectRatio:ratio_low should be greater than zero {self.ratio_low}'
        assert self.ratio_high > self.ratio_low, f'AspectRatio:ratio_high {self.ratio_high} should be greater than ratio_low {self.ratio_low}'

        bvar = checker.bbox_vars(self.subcircuit, is_subcircuit=True)
        checker.append(checker.cast(bvar.urx-bvar.llx, float) >= self.ratio_low*checker.cast(bvar.ury-bvar.lly, float))
        checker.append(checker.cast(bvar.urx-bvar.llx, float) < self.ratio_high*checker.cast(bvar.ury-bvar.lly, float))


class Boundary(HardConstraint):
    """
    Define `max_height` and/or `max_width` on a subcircuit in micrometers.
    """
    subcircuit: str
    max_width: Optional[float]
    max_height: Optional[float]

    def check(self, checker):
        bvar = checker.bbox_vars(self.subcircuit, is_subcircuit=True)

        if self.max_width is not None:
            assert self.max_width >= 0, f'Boundary:max_width should be greater than zero {self.max_width}'
            checker.append(checker.cast(bvar.urx-bvar.llx, float) <= self.max_width)

        if self.max_height is not None:
            assert self.max_height >= 0, f'Boundary:max_height should be greater than zero {self.max_height}'
            checker.append(checker.cast(bvar.urx-bvar.llx, float) <= self.max_height)


class MultiConnection(SoftConstraint):
    nets: List[str]
    multiplier: int


ConstraintType = Union[
    # ALIGN Internal DSL
    Order, Align,
    Enclose, Spread,
    SetBoundingBox,
    # Additional helper constraints
    AlignInOrder,
    # Current Align constraints
    # Consider removing redundant ones
    CreateAlias,
    GroupBlocks,
    MatchBlocks,
    BlockDistance,
    HorizontalDistance,
    VerticalDistance,
    GuardRing,
    SymmetricBlocks,
    GroupCaps,
    NetConst,
    PortLocation,
    SymmetricNets,
    AspectRatio,
    Boundary,
    MultiConnection
]


class ConstraintDB(types.List[ConstraintType]):

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr(None)

    def _check(self, constraint):
        if self._checker and hasattr(constraint, 'check'):
            try:
                constraint.check(self._checker)
            except checker.CheckerError as e:
                logger.error(f'Checker raised error:\n {e}')
                logger.error(f'Failed to add constraint {constraint} due to conflict with one or more of:')
                for c in self.__root__:
                    if hasattr(c, 'check'):
                        logger.error(c)
                raise e


    def _check_recursive(self, constraints):
        for constraint in expand_user_constraints(constraints):
            self._check(constraint)

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        self._check_recursive([constraint])
        super().append(constraint)

    def __init__(self, *args, **kwargs):
        if len(args) == 0 and '__root__' not in kwargs:
            kwargs['__root__'] = []
        elif len(args) == 1:
            kwargs['__root__'] = args[0]
            args = tuple()
        super().__init__(*args, **kwargs)
        if checker.Z3Checker.enabled:
            self._checker = checker.Z3Checker()
            self._check_recursive(self.__root__)

    def checkpoint(self):
        if self._checker:
            self._checker.checkpoint()
        return super().checkpoint()

    def _revert(self):
        if self._checker:
            self._checker.revert()
        super()._revert()


def expand_user_constraints(const_list):
    for const in const_list:
        if hasattr(const, 'yield_constraints'):
            yield from expand_user_constraints(const.yield_constraints())
        else:
            yield const
