import abc
import more_itertools as itertools
import re

from . import types
from .types import Union, Optional, Literal, List, set_context
from . import checker

import logging
logger = logging.getLogger(__name__)

pattern = re.compile(r'(?<!^)(?=[A-Z])')


def get_instances_from_hacked_dataclasses(constraint):
    assert constraint.parent.parent is not None, 'Cannot access parent scope'
    if hasattr(constraint.parent.parent, 'graph'):
        instances = {k for k, v in constraint.parent.parent.graph.nodes.items() if v['inst_type'] != 'net'}
    elif hasattr(constraint.parent.parent, 'elements'):
        instances = {x.name for x in constraint.parent.parent.elements}
    elif hasattr(constraint.parent.parent, 'instances'):
        instances = {x.instance_name for x in constraint.parent.parent.instances}
    else:
        raise NotImplementedError(f"Cannot handle {type(constraint.parent.parent)}")
    names = {x.name for x in constraint.parent if hasattr(x, 'name')}
    return set.union(instances, names)


def validate_instances(cls, value):
    # instances = cls._validator_ctx().parent.parent.instances
    instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
    assert isinstance(instances, set), 'Could not retrieve instances from subcircuit definition'
    assert all(x in instances or x.upper() in instances for x in value), f'One or more constraint instances {value} not found in {instances}'
    return value


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
          MUST implement this function.

        Function must yield a list of mathematical
          expressions supported by the 'checker'
          backend. This can be done using multiple
          'yield' statements or returning an iterable
          object such as list
        '''
        pass


class UserConstraint(HardConstraint, abc.ABC):

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

    def check(self, checker):
        for constraint in self.yield_constraints():
            yield from constraint.check(checker)


class Order(HardConstraint):
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

    @types.validator('instances', allow_reuse=True)
    def order_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

    def check(self, checker):

        def cc(b1, b2, c='x'):  # Create coordinate constraint
            if self.abut:
                return getattr(b1, f'ur{c}') == getattr(b2, f'll{c}')
            else:
                return getattr(b1, f'ur{c}') <= getattr(b2, f'll{c}')

        bvars = checker.iter_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.direction == 'left_to_right':
                yield cc(b1, b2, 'x')
            elif self.direction == 'right_to_left':
                yield cc(b2, b1, 'x')
            elif self.direction == 'bottom_to_top':
                yield cc(b1, b2, 'y')
            elif self.direction == 'top_to_bottom':
                yield cc(b2, b1, 'y')
            elif self.direction == 'horizontal':
                yield checker.Or(
                    cc(b1, b2, 'x'),
                    cc(b2, b1, 'x'))
            elif self.direction == 'vertical':
                yield checker.Or(
                    cc(b1, b2, 'y'),
                    cc(b2, b1, 'y'))
            else:
                yield checker.Or(
                    cc(b1, b2, 'x'),
                    cc(b2, b1, 'x'),
                    cc(b1, b2, 'y'),
                    cc(b2, b1, 'y'))


class Align(HardConstraint):
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

    _inst_validator = types.validator('instances', allow_reuse=True)(validate_instances)

    @types.validator('instances', allow_reuse=True)
    def align_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

    def check(self, checker):
        bvars = checker.iter_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'h_top':
                yield b1.ury == b2.ury
            elif self.line == 'h_bottom':
                yield b1.lly == b2.lly
            elif self.line == 'h_center':
                yield (b1.lly + b1.ury) / 2 == (b2.lly + b2.ury) / 2
            elif self.line == 'h_any':
                yield checker.Or(  # We don't know which bbox is higher yet
                    checker.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                    checker.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                )
            elif self.line == 'v_left':
                yield b1.llx == b2.llx
            elif self.line == 'v_right':
                yield b1.urx == b2.urx
            elif self.line == 'v_center':
                yield (b1.llx + b1.urx) / 2 == (b2.llx + b2.urx) / 2
            elif self.line == 'v_any':
                yield checker.Or(  # We don't know which bbox is wider yet
                    checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                    checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx)
                )
            else:
                yield checker.Or(  # h_any OR v_any
                    checker.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                    checker.And(b2.urx <= b1.urx, b2.llx >= b1.llx),
                    checker.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                    checker.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
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
    instances: Optional[List[str]]
    min_height: Optional[int]
    max_height: Optional[int]
    min_width: Optional[int]
    max_width: Optional[int]
    min_aspect_ratio: Optional[float]
    max_aspect_ratio: Optional[float]

    _inst_validator = types.validator('instances', allow_reuse=True)(validate_instances)

    @types.validator('max_aspect_ratio', allow_reuse=True)
    def bound_in_box_optional_fields(cls, value, values):
        assert value or any(
            getattr(values, x, None)
            for x in (
                'min_height',
                'max_height',
                'min_width',
                'max_width',
                'min_aspect_ratio'
            )
        ), 'Too many optional fields'
        return value

    def check(self, checker):
        bb = checker.bbox_vars(checker.label(self))
        if self.min_width:
            yield bb.urx - bb.llx >= self.min_width
        if self.min_height:
            yield bb.ury - bb.lly >= self.min_height
        if self.max_width:
            yield bb.urx - bb.llx <= self.max_width
        if self.max_height:
            yield bb.ury - bb.lly <= self.max_height
        if self.min_aspect_ratio:
            yield checker.cast(
                (bb.ury - bb.lly) / (bb.urx - bb.llx),
                float) >= self.min_aspect_ratio
        if self.max_aspect_ratio:
            yield checker.cast(
                (bb.ury - bb.lly) / (bb.urx - bb.llx),
                float) <= self.max_aspect_ratio
        bvars = checker.iter_bbox_vars(self.instances)
        for b in bvars:
            yield b.urx <= bb.urx
            yield b.llx >= bb.llx
            yield b.ury <= bb.ury
            yield b.lly >= bb.lly


class Spread(HardConstraint):
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

    @types.validator('instances', allow_reuse=True)
    def spread_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

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

        bvars = checker.iter_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.direction == 'horizontal':
                yield cc(b1, b2, 'x')
            elif self.direction == 'vertical':
                yield cc(b1, b2, 'y')
            else:
                yield checker.Or(
                    cc(b1, b2, 'x'),
                    cc(b1, b2, 'y')
                )


class SetBoundingBox(HardConstraint):
    instance: str
    llx: int
    lly: int
    urx: int
    ury: int
    is_subcircuit: Optional[bool] = False

    @types.validator('urx', allow_reuse=True)
    def x_is_valid(cls, value, values):
        assert value > values['llx'], f'Reflection is not supported yet'
        return value

    @types.validator('ury', allow_reuse=True)
    def y_is_valid(cls, value, values):
        assert value > values['lly'], f'Reflection is not supported yet'
        return value

    def check(self, checker):
        bvar = checker.bbox_vars(self.instance, is_subcircuit=self.is_subcircuit)
        yield bvar.llx == self.llx
        yield bvar.lly == self.lly
        yield bvar.urx == self.urx
        yield bvar.ury == self.ury


class AspectRatio(HardConstraint):
    """
    Define lower and upper bounds on aspect ratio (=width/height) of a subcircuit

    `ratio_low` <= width/height <= `ratio_high`
    """
    subcircuit: str
    ratio_low: float = 0.1
    ratio_high: float = 10
    weight: int = 1

    @types.validator('ratio_low', allow_reuse=True)
    def ratio_low_validator(cls, value):
        assert value >= 0, f'AspectRatio:ratio_low should be greater than zero {value}'
        return value

    @types.validator('ratio_high', allow_reuse=True)
    def ratio_high_validator(cls, value, values):
        assert value > values['ratio_low'], f'AspectRatio:ratio_high {value} should be greater than ratio_low {values["ratio_low"]}'
        return value

    def check(self, checker):
        bvar = checker.bbox_vars(self.subcircuit, is_subcircuit=True)
        yield checker.cast(bvar.urx-bvar.llx, float) >= self.ratio_low * checker.cast(bvar.ury-bvar.lly, float)
        yield checker.cast(bvar.urx-bvar.llx, float) < self.ratio_high * checker.cast(bvar.ury-bvar.lly, float)


class Boundary(HardConstraint):
    """
    Define `max_height` and/or `max_width` on a subcircuit in micrometers.
    """
    subcircuit: str
    max_width: Optional[float] = 10000
    max_height: Optional[float] = 10000

    @types.validator('max_width', allow_reuse=True)
    def max_width_validator(cls, value):
        assert value >= 0, f'Boundary:max_width should be greater than zero {value}'
        return value

    @types.validator('max_height', allow_reuse=True)
    def max_height_validator(cls, value):
        assert value >= 0, f'Boundary:max_height should be greater than zero {value}'
        return value

    def check(self, checker):
        bvar = checker.bbox_vars(self.subcircuit, is_subcircuit=True)
        if self.max_width is not None:
            yield checker.cast(bvar.urx-bvar.llx, float) <= 1000*self.max_width  # in nanometer
        if self.max_height is not None:
            yield checker.cast(bvar.ury-bvar.lly, float) <= 1000*self.max_height  # in nanometer


# You may chain constraints together for more complex constraints by
#     1) Assigning default values to certain attributes
#     2) Using custom validators to modify attribute values
# Note: Do not implement check() here. It will be ignored.
#       Only ALIGN internal constraints may be translated

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
        with set_context(self._parent):
            yield Align(
                instances=self.instances,
                line=f'{self.direction[0]}_{self.line}'
            )
            yield Order(
                instances=self.instances,
                direction='left_to_right' if self.direction == 'horizontal' else 'top_to_bottom',
                abut=self.abut
            )


#
# list of 'SoftConstraint'
#
# Below is a list of legacy constraints
# that have not been hardened yet
#

class PlaceSymmetric(SoftConstraint):
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

    @types.validator('instances', allow_reuse=True)
    def place_symmetric_instances_validator(cls, value):
        '''
        X = Align(2, 3, 'h_center')
        Y = Align(4, 5, 'h_center')
        Align(1, X, Y, 6, 'center')

        '''
        assert len(value) >= 1, 'Must contain at least one instance'
        assert all(isinstance(x, List) for x in value), f'All arguments must be of type list in {self.instances}'
        return value


class SameTemplate(SoftConstraint):
    instances: List[str]


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


class PowerPorts(SoftConstraint):
    '''
    power port for each hieararchy
    '''
    ports: List[str]


class GroundPorts(SoftConstraint):
    '''
    Ground port for each hieararchy
    '''
    ports: List[str]


class ClockPorts(SoftConstraint):
    '''
    Clock port for each hieararchy
    '''
    ports: List[str]


class DoNotUseLib(SoftConstraint):
    '''
    Primitive libraries which should not be used
    '''
    libraries: List[str]
    propagate : Optional[bool]


class IsDigital(SoftConstraint):
    '''
    Place this block digitally
    Forbids any preprocessing, auto-annotation, array-identification or auto-constraint generation
    '''
    isTrue: bool
    propagate : Optional[bool]


class AutoConstraint(SoftConstraint):
    '''
    Forbids/Allow any auto-constraint generation
    '''
    isTrue: bool
    propagate : Optional[bool]


class IdentifyArray(SoftConstraint):
    '''
    Forbids/Alow any array identification
    '''
    isTrue: bool
    propagate : Optional[bool]


class AutoGroupCaps(SoftConstraint):
    '''
    Forbids/Allow creation of arrays for symmetric caps
    '''
    isTrue: bool
    propagate : Optional[bool]


class FixSourceDrain(SoftConstraint):
    '''
    Checks the netlist for any source/drain interchange.
    Traverses and fix them based on power to gnd traversal
    '''
    isTrue: bool
    propagate : Optional[bool]


class KeepDummyHierarchies(SoftConstraint):
    '''
    Removes any single instance hierarchies
    '''
    isTrue: bool
    propagate : Optional[bool]


class MergeSeriesDevices(SoftConstraint):
    '''
    Allow stacking of series devices
    Only works on NMOS/PMOS/CAP/RES
    '''
    isTrue: bool
    propagate : Optional[bool]


class MergeParallelDevices(SoftConstraint):
    '''
    Allow merging of parallel devices
    Only works on NMOS/PMOS/CAP/RES
    '''
    isTrue: bool
    propagate : Optional[bool]


class DoNotIdentify(SoftConstraint):
    '''
    TODO: Can be replicated by Enclose??
    '''
    instances: List[str]


class SymmetricBlocks(SoftConstraint):
    pairs: List[List[str]]
    direction: Literal['H', 'V']

    @types.validator('pairs', allow_reuse=True)
    def pairs_validator(cls, value):
        '''
        X = Align(2, 3, 'h_center')
        Y = Align(4, 5, 'h_center')
        Align(1, X, Y, 6, 'center')

        '''
        instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        for pair in value:
            assert len(pair) >= 1, 'Must contain at least one instance'
            assert len(pair) <= 2, 'Must contain at most two instances'
            validate_instances(cls, pair)
        if not hasattr(cls._validator_ctx().parent.parent, 'elements'):
            # PnR stage VerilogJsonModule
            return value
        if len(cls._validator_ctx().parent.parent.elements)==0:
            #skips the check while reading user constraints
            return value
        group_block_instances = [const.name for const in cls._validator_ctx().parent if isinstance(const, GroupBlocks)]
        for pair in value:
            # logger.debug(f"pairs {self.pairs} {self.parent.parent.get_element(pair[0])}")
            if len([ele for ele in pair if ele in group_block_instances])>0:
                #Skip check for group block elements as they are added later in the flow
                continue
            elif len(pair)==2:
                assert cls._validator_ctx().parent.parent.get_element(pair[0]), f"element {pair[0]} not found in design"
                assert cls._validator_ctx().parent.parent.get_element(pair[1]), f"element {pair[1]} not found in design"
                assert cls._validator_ctx().parent.parent.get_element(pair[0]).parameters == \
                    cls._validator_ctx().parent.parent.get_element(pair[1]).parameters, \
                        f"Incorrent symmetry pair {pair} in subckt {cls._validator_ctx().parent.parent.name}"
        return value


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


class MultiConnection(SoftConstraint):
    nets: List[str]
    multiplier: int


ConstraintType = Union[
    # ALIGN Internal DSL
    Order, Align,
    Enclose, Spread,
    SetBoundingBox,
    AspectRatio,
    Boundary,
    # Additional User constraints
    AlignInOrder,
    # Legacy Align constraints
    # (SoftConstraints)
    SameTemplate,
    CreateAlias,
    GroupBlocks,
    MatchBlocks,
    DoNotIdentify,
    BlockDistance,
    HorizontalDistance,
    VerticalDistance,
    GuardRing,
    SymmetricBlocks,
    GroupCaps,
    NetConst,
    PortLocation,
    SymmetricNets,
    MultiConnection,
    # Setup constraints
    PowerPorts,
    GroundPorts,
    ClockPorts,
    DoNotUseLib,
    IsDigital,
    AutoConstraint,
    AutoGroupCaps,
    FixSourceDrain,
    KeepDummyHierarchies,
    MergeSeriesDevices,
    MergeParallelDevices,
    IdentifyArray
]


class ConstraintDB(types.List[ConstraintType]):

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr(None)

    def _check(self, constraint):
        assert constraint.parent is not None, 'parent is not set'
        assert constraint.parent.parent is not None, 'parent.parent is not set'
        if self._checker and hasattr(constraint, 'check'):
            generator = constraint.check(self._checker)
            if generator is None:
                raise NotImplementedError(f'{constraint}.check() did not return a valid generator')
            formulae = list(generator)
            if len(formulae) == 0:
                raise NotImplementedError(f'{constraint}.check() yielded an empty list of expressions')
            try:
                self._checker.append(
                    self._checker.And(
                        *formulae
                    ) if len(formulae) > 1 else formulae[0],
                    label=self._checker.label(constraint)
                )
            except checker.CheckerError as e:
                logger.debug(f'Checker raised error:\n {e}')
                assert self._checker.label(constraint) in e.labels, "Something went terribly wrong. Current constraint not in unsat core"
                core = [x.json() for x in self.__root__ if self._checker.label(x) in e.labels and x != constraint]
                logger.error(f'Failed to add constraint {constraint.json()}')
                logger.error(f'   due to conflict with {core}')
                raise checker.CheckerError(f'Failed to add constraint {constraint.json()} due to conflict with {core}')

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        super().append(constraint)
        self._check(self.__root__[-1])

    @types.validate_arguments
    def remove(self, constraint: ConstraintType):
        super().remove(constraint)

    def __init__(self, *args, check=True, **kwargs):
        super().__init__()
        if check:
            self._checker = checker.Z3Checker()
        # Constraints may need to access parent scope for subcircuit information
        # To ensure parent is set appropriately, force users to use append
        if '__root__' in kwargs:
            data = kwargs['__root__']
            del kwargs['__root__']
        elif len(args) == 1:
            data = args[0]
            args = tuple()
        else:
            assert len(args) == 0 and len(kwargs) == 0
            data = []
        with set_context(self):
            for x in data:
                if x['constraint'] == 'GroupBlocks':
                    logger.info(f'first reading groupblock data {x}')
                    self.append(x)
            for x in data:
                if x['constraint'] != 'GroupBlocks':
                    logger.info(f'reading rest data {x}')
                    self.append(x)

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
            with types.set_context(const.parent):
                yield from const.yield_constraints()
        else:
            yield const
