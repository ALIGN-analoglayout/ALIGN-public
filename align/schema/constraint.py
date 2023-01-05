import abc
import more_itertools as itertools
import itertools as plain_itertools
import re
import logging

from . import types
from .types import BaseModel, Union, Optional, Literal, List, set_context

from pydantic import Field


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
    elif type(constraint.parent.parent).__name__ == "GroupBlocks":
        return get_instances_from_hacked_dataclasses(constraint.parent.parent)
    else:
        raise NotImplementedError(f"Cannot handle {type(constraint.parent.parent)}")
    names1 = {x.instance_name for x in constraint.parent if hasattr(x, 'instance_name')}  # group block
    names2 = {x.name for x in constraint.parent if hasattr(x, 'name')}  # group_cap, alias
    return set.union(instances, names1, names2)


def validate_instances(cls, value):
    # instances = cls._validator_ctx().parent.parent.instances
    instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
    assert isinstance(instances, set), 'Could not retrieve instances from subcircuit definition'
    for x in value:  # explicit loop to point out the not found instance
        assert x in instances or x.upper() in instances, f"Instance {x} not found in the circuit"
    return [x.upper() for x in value]


def validate_ports(cls, value):
    constraint = cls._validator_ctx()
    if constraint.parent and constraint.parent.parent:
        obj = constraint.parent.parent
        # VerilogJson modules do not always have power pins due to power pin removal hack.
        # isinstance avoided due to circular import
        if hasattr(obj, "pins"):
            pins = obj.pins
            for v in value:
                assert v in pins, f"Port {v} not found in subcircuit {obj.name.lower()}"
    return value


def upper_case(cls, value):
    return [v.upper() for v in value]


def upper_case_str(cls, value):
    return value.upper()


def assert_non_negative(cls, value):
    assert value >= 0, f'Value must be non-negative: {value}'
    return value


class SoftConstraint(types.BaseModel):

    constraint: str

    def __init__(self, *args, **kwargs):
        # constraint = pattern.sub(
        #     '__', self.__class__.__name__).lower()
        constraint = self.__class__.__name__
        if 'constraint' not in kwargs or kwargs['constraint'] == self.__class__.__name__:
            kwargs['constraint'] = constraint
        else:
            assert constraint == kwargs[
                'constraint'], f'Unexpected `constraint` {kwargs["constraint"]} (expected {constraint})'
        super().__init__(*args, **kwargs)


class HardConstraint(SoftConstraint, abc.ABC):

    @abc.abstractmethod
    def translate(self, solver):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from HardConstraint
          MUST implement this function.

        Function must yield a list of mathematical
          expressions supported by the 'solver'
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

    def translate(self, solver):
        for constraint in self.yield_constraints():
            if isinstance(constraint, HardConstraint):
                yield from constraint.translate(solver)


class Order(HardConstraint):
    '''
    Defines a placement order for instances in a subcircuit.

    Args:
        instances (list[str]): List of :obj:`instances`
        direction (str, optional): The following options for direction are supported

            :obj:`'horizontal'`, placement order is left to right or vice-versa.

            :obj:`'vertical'`,  placement order is bottom to top or vice-versa.

            :obj:`'left_to_right'`, placement order is left to right.

            :obj:`'right_to_left'`, placement order is right to left.

            :obj:`'bottom_to_top'`, placement order is bottom to top.

            :obj:`'top_to_bottom'`, placement order is top to bottom.

            :obj:`None`: default (:obj:`'horizontal'` or :obj:`'vertical'`)
        abut (bool, optional): If `abut` is `true` adjoining instances will touch

    .. image:: ../images/OrderBlocks.PNG
        :align: center

    WARNING: `Order` does not imply aligment / overlap
    of any sort (See `Align`)

    Example: ::

        {"constraint":"Order", "instances": ['MN0', 'MN1', 'MN2'], "direction": "left_to_right"}

    '''
    instances: List[str]
    direction: Optional[Literal[
        'horizontal', 'vertical',
        'left_to_right', 'right_to_left',
        'bottom_to_top', 'top_to_bottom'
    ]]
    abut: bool = False
    _instance_attribute: str = "instances"

    @types.validator('instances', allow_reuse=True)
    def order_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

    def translate(self, solver):

        def cc(b1, b2, c='x'):  # Create coordinate constraint
            if self.abut:
                return getattr(b1, f'ur{c}') == getattr(b2, f'll{c}')
            else:
                return getattr(b1, f'ur{c}') <= getattr(b2, f'll{c}')

        bvars = solver.iter_bbox_vars(self.instances)
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
                yield solver.Or(
                    cc(b1, b2, 'x'),
                    cc(b2, b1, 'x'))
            elif self.direction == 'vertical':
                yield solver.Or(
                    cc(b1, b2, 'y'),
                    cc(b2, b1, 'y'))
            else:
                yield solver.Or(
                    cc(b1, b2, 'x'),
                    cc(b2, b1, 'x'),
                    cc(b1, b2, 'y'),
                    cc(b2, b1, 'y'))

    def yield_constraints(self):
        yield DoNotIdentify(instances=self.instances)


class Align(HardConstraint):
    '''
    `Instances` will be aligned along `line`. Could be
    strict or relaxed depending on value of `line`

    Args:
        instances (list[str]): List of `instances`
        line (str, optional): The following `line` values are currently supported:

            :obj:`h_any`, align instance's top, bottom or anything in between.

            :obj:`'v_any'`, align instance's left, right or anything in between.

            :obj:`'h_top'`, align instance's horizontally based on top.

            :obj:`'h_bottom'`, align instance's horizomtally based on bottom.

            :obj:`'h_center'`, align instance's horizontally based on center.

            :obj:`'v_left'`, align instance's vertically based on left.

            :obj:`'v_right'`, align instance's vertically based on right.

            :obj:`'v_center'`, align instance's vertically based on center.

            :obj:`None`:default (:obj:`'h_any'` or :obj:`'v_any'`).

    .. image:: ../images/AlignBlocks.PNG
        :align: center

    WARNING: `Align` does not imply ordering of any sort
    (See `Order`)

    Example: ::

        {"constraint":"Align", "instances": ['MN0', 'MN1', 'MN2'], "line": "v_center"}

    '''
    instances: List[str]
    line: Optional[Literal[
        'h_any', 'h_top', 'h_bottom', 'h_center',
        'v_any', 'v_left', 'v_right', 'v_center'
    ]]
    _instance_attribute: str = "instances"

    _inst_validator = types.validator('instances', allow_reuse=True)(validate_instances)

    @types.validator('instances', allow_reuse=True)
    def align_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

    def translate(self, solver):
        bvars = solver.iter_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'h_top':
                yield b1.ury == b2.ury
            elif self.line == 'h_bottom':
                yield b1.lly == b2.lly
            elif self.line == 'h_center':
                yield (b1.lly + b1.ury) / 2 == (b2.lly + b2.ury) / 2
            elif self.line == 'h_any':
                yield solver.Or(  # We don't know which bbox is higher yet
                    solver.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                    solver.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                )
            elif self.line == 'v_left':
                yield b1.llx == b2.llx
            elif self.line == 'v_right':
                yield b1.urx == b2.urx
            elif self.line == 'v_center':
                yield (b1.llx + b1.urx) / 2 == (b2.llx + b2.urx) / 2
            elif self.line == 'v_any':
                yield solver.Or(  # We don't know which bbox is wider yet
                    solver.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                    solver.And(b2.urx <= b1.urx, b2.llx >= b1.llx)
                )
            else:
                yield solver.Or(  # h_any OR v_any
                    solver.And(b1.urx <= b2.urx, b1.llx >= b2.llx),
                    solver.And(b2.urx <= b1.urx, b2.llx >= b1.llx),
                    solver.And(b1.lly >= b2.lly, b1.ury <= b2.ury),
                    solver.And(b2.lly >= b1.lly, b2.ury <= b1.ury)
                )

    def yield_constraints(self):
        yield DoNotIdentify(instances=self.instances)


class Spread(HardConstraint):
    '''
    Spread `instances` by forcing minimum spacing along `direction`
    if a pair of instances overlap in the orthogonal direction

    Args:
        instances (list[str]): List of `instances`
        direction (str, optional): Direction for placement spread.
            (:obj:`'horizontal'` or :obj:`'vertical'` or :obj:`None`)
        distance (int): Distance in nanometer

    WARNING: This constraint checks for overlap but
    doesn't enforce it (See `Align`)

    Example: ::

        {
            "constraint": "Spread",
            "instances": ['MN0', 'MN1', 'MN2'],
            "direction": horizontal,
            "distance": 100
        }
    '''

    instances: List[str]
    direction: Literal['horizontal', 'vertical']
    distance: int  # in nm

    @types.validator('instances', allow_reuse=True)
    def spread_instances_validator(cls, value):
        assert len(value) >= 2, 'Must contain at least two instances'
        return validate_instances(cls, value)

    def translate(self, solver):

        def cc(b1, b2, d='x'):
            od = 'y' if d == 'x' else 'x'
            return solver.Implies(
                solver.And(  # overlap in orthogonal direction od
                    getattr(b1, f'ur{od}') > getattr(b2, f'll{od}'),
                    getattr(b2, f'ur{od}') > getattr(b1, f'll{od}'),
                ),
                solver.And(  # distance between sidewalls in direction d
                    solver.Abs(getattr(b1, f'll{d}') - getattr(b2, f'ur{d}')) >= self.distance,
                    solver.Abs(getattr(b2, f'll{d}') - getattr(b1, f'ur{d}')) >= self.distance,
                )
            )

        bvars = solver.iter_bbox_vars(self.instances)
        for b1, b2 in plain_itertools.combinations(bvars, 2):
            if self.direction == 'horizontal':
                yield cc(b1, b2, 'x')
            elif self.direction == 'vertical':
                yield cc(b1, b2, 'y')
            else:
                assert False, "Please speficy direction"

    def yield_constraints(self):
        yield DoNotIdentify(instances=self.instances)


class AssignBboxVariables(HardConstraint):
    bbox_name: str
    llx: int
    lly: int
    urx: int
    ury: int

    @types.validator('urx', allow_reuse=True)
    def x_is_valid(cls, value, values):
        assert value > values['llx'], 'Reflection is not supported yet'
        return value

    @types.validator('ury', allow_reuse=True)
    def y_is_valid(cls, value, values):
        assert value > values['lly'], 'Reflection is not supported yet'
        return value

    def translate(self, solver):
        bvar = solver.bbox_vars(self.bbox_name)
        yield bvar.llx == self.llx
        yield bvar.lly == self.lly
        yield bvar.urx == self.urx
        yield bvar.ury == self.ury


class AspectRatio(HardConstraint):
    """
    Define lower and upper bounds on aspect ratio (=width/height) of a subcircuit

    `ratio_low` <= width/height <= `ratio_high`

    Args:
        ratio_low (float): Minimum aspect ratio (default 0.1)
        ratio_high (float): Maximum aspect ratio (default 10)
        weight (int): Weigth of this constraint (default 1)

    Example: ::

        {"constraint": "AspectRatio", "ratio_low": 0.1, "ratio_high": 10, "weight": 1 }
    """
    ratio_low: float = 0.1
    ratio_high: float = 10
    weight: int = 1

    _ratio_low_validator = types.validator('ratio_low', allow_reuse=True)(assert_non_negative)

    @types.validator('ratio_high', allow_reuse=True)
    def ratio_high_validator(cls, value, values):
        assert value > values['ratio_low'], f'AspectRatio:ratio_high {value} should be greater than ratio_low {values["ratio_low"]}'
        return value

    def translate(self, solver):
        bvar = solver.bbox_vars('subcircuit')
        yield solver.cast(bvar.urx-bvar.llx, float) >= self.ratio_low * solver.cast(bvar.ury-bvar.lly, float)
        yield solver.cast(bvar.urx-bvar.llx, float) < self.ratio_high * solver.cast(bvar.ury-bvar.lly, float)


class Boundary(HardConstraint):
    """
    Define `max_height` and/or `max_width` on a subcircuit in micrometers.

    Args:
        max_width (float, Optional) = 10000
        max_height (float, Optional) = 10000

    Example: ::

        {"constraint": "Boundary", "max_height": 100 }
    """
    max_width: Optional[float] = 100000  # 100mm
    max_height: Optional[float] = 100000  # 100mm
    halo_horizontal: Optional[float] = 0
    halo_vertical: Optional[float] = 0

    _max_width = types.validator('max_width', allow_reuse=True)(assert_non_negative)
    _max_height = types.validator('max_height', allow_reuse=True)(assert_non_negative)
    _halo_horizontal = types.validator('halo_horizontal', allow_reuse=True)(assert_non_negative)
    _halo_vertical = types.validator('halo_vertical', allow_reuse=True)(assert_non_negative)

    @types.validator('halo_horizontal', 'halo_horizontal', allow_reuse=True)
    def validate_halo(cls, value, values, field):
        if field.name == 'halo_horizontal':
            key = 'max_width'
        else:
            key = 'max_height'
        assert values[key] > value, f'Halo should be smaller than the {key}'
        return value

    def translate(self, solver):
        bbox = solver.bbox_vars('subcircuit')
        yield solver.cast(bbox.urx-bbox.llx, float) <= 1000*self.max_width  # convert to nanometer
        yield solver.cast(bbox.ury-bbox.lly, float) <= 1000*self.max_height  # convert to nanometer

        instances = get_instances_from_hacked_dataclasses(self)
        bvars = solver.iter_bbox_vars(instances)
        for b in bvars:
            yield b.llx >= bbox.llx + int(1000*self.halo_horizontal)
            yield b.urx <= bbox.urx - int(1000*self.halo_horizontal)
            yield b.lly >= bbox.lly + int(1000*self.halo_vertical)
            yield b.ury <= bbox.ury - int(1000*self.halo_vertical)

# You may chain constraints together for more complex constraints by
#     1) Assigning default values to certain attributes
#     2) Using custom validators to modify attribute values
# Note: Do not implement translate() here as it may be ignored
#       by certain engines


class AlignInOrder(UserConstraint):
    '''
    Align `instances` on `line` ordered along `direction`

    Args:
        instances (list[str]): List of :obj:`instances`
        line (str, optional): The following `line` values are currently supported:

            :obj:`'top'`, align instance's horizontally based on top.

            :obj:`'bottom'`, align instance's horizomtally based on bottom.

            :obj:`'center'`, align instance's horizontally based on center.

            :obj:`'left'`, align instance's vertically based on left.

            :obj:`'right'`, align instance's vertically based on right.
        direction: The following `direction` values are supported:

            :obj: `'horizontal'`, left to right

            :obj: `'vertical'`, bottom to top

    Example: ::

        {
            "constraint":"Align",
            "instances": ["MN0", "MN1", "MN3"],
            "line": "center",
            "direction": "horizontal"
        }

    Note: This is a user-convenience constraint. Same
    effect can be realized using `Order` & `Align`

    '''
    instances: List[str]
    line: Literal[
        'top', 'bottom',
        'left', 'right',
        'center'
    ] = 'bottom'
    direction: Optional[Literal['horizontal', 'vertical']]
    abut: bool = False
    _instance_attribute: str = "instances"

    @types.validator('direction', allow_reuse=True, always=True)
    def _direction_depends_on_line(cls, v, values):
        # Process unambiguous line values
        if values['line'] in ['bottom', 'top']:
            if v is None:
                v = 'horizontal'
            else:
                assert v == 'horizontal', \
                    'direction is horizontal if line is bottom or top'
        elif values['line'] in ['left', 'right']:
            if v is None:
                v = 'vertical'
            else:
                assert v == 'vertical', \
                    'direction is vertical if line is left or right'
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
            yield DoNotIdentify(instances=self.instances)


class Floorplan(UserConstraint):
    '''
    Row-based layout floorplan from top to bottom
    Instances on each row are ordered from left to right.

    Example: Define three regions and assign each instance to a region:
        {"constraint":"Floorplan", "regions": [["A", "B", "C"], ["D", "E"], ["G"], "order": true}

        -----
        A B C
        -----
        D E
        -----
        G
        -----
    '''
    regions: List[List[str]]
    order: bool = False
    symmetrize: bool = False
    _instance_attribute: str = "regions"

    @types.validator('regions', allow_reuse=True, always=True)
    def _check_instance(cls, value):
        new_rows = list()
        for row in value:
            new_rows.append(validate_instances(cls, row))
        return new_rows

    def yield_constraints(self):
        above_below = set()
        with set_context(self._parent):
            logger.debug("=== Floorplan ========================")
            # Regions from top to bottom
            logger.debug("===========================")
            for i in range(len(self.regions)-1):
                for [above, below] in plain_itertools.product(self.regions[i], self.regions[i+1]):
                    logger.debug(f'Above:{above} Below:{below}')
                    above_below.add((above, below))
                    assert (below, above) not in above_below, \
                        f'Please review floorplan constraint:\n{self.regions}.\n{below} is previously placed above {above}.'
                    yield Order(instances=[above, below], direction='top_to_bottom', abut=False)
            # Order instances in each region from left to right
            if self.order:
                logger.debug("===========================")
                for region in self.regions:
                    logger.debug(f'Order left to right: {region}')
                    if len(region) > 1:
                        yield Order(instances=region, direction='left_to_right', abut=False)
            # Symmetrize instances along a single vertical line
            if self.symmetrize:
                logger.debug("===========================")
                pairs = list()
                for region in self.regions:
                    if len(region) <= 2:
                        pairs.append(region)
                    else:
                        for i in range(len(region)//2):
                            pairs.append([region[i], region[-1-i]])
                        if len(region) % 2 == 1:
                            pairs.append([region[i+1]])
                logger.debug(f'Symmetric blocks:\n{pairs}')
                yield SymmetricBlocks(pairs=pairs, direction='V')
            # Do not identify these instances if both ordered and symmetric
            if self.symmetrize and self.order:
                instances = list()
                for region in self.regions:
                    instances.extend(region)
                yield DoNotIdentify(instances=instances)


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
    `instances` = [['1'], ['4', '5'], ['2', '3'], ['6']]
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
        assert all(isinstance(x, List) for x in value), f'All arguments must be of type list in {cls.instances}'
        return value


class CompactPlacement(SoftConstraint):
    """CompactPlacement

    Defines snapping position of placement for all blocks in design.

    Args:
        style (str): Following options are available.

            :obj:`'left'`, Moves all instances towards left during post-processing of placement.

            :obj:`'right'`, Moves all instances towards right during post-processing of placement.

            :obj:`'center'`, Moves all instances towards center during post-processing of placement.

    Example: ::

        {"constraint": "CompactPlacement", "style": "center"}
    """
    style: Literal[
        'left', 'right',
        'center'
    ] = 'left'


class SameTemplate(SoftConstraint):
    """SameTemplate

    Makes identical copy of all isntances

    Args:
        instances (list[str]): List of :obj:`instances`

    Example: ::

        {"constraint":"SameTemplate", "instances": ["MN0", "MN1", "MN3"]}
    """
    instances: List[str]
    _instance_attribute: str = "instances"

    @types.validator("instances", allow_reuse=True)
    def instances_validator(cls, instances):

        # logger.debug(f"SameTemplate {instances=}")
        # assert len(instances) >= 2, "SameTemplate constraint requires at least two instances"

        _ = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        instances = validate_instances(cls, instances)

        if not hasattr(cls._validator_ctx().parent.parent, 'elements'):
            # PnR stage VerilogJsonModule
            return instances
        if len(cls._validator_ctx().parent.parent.elements) == 0:
            # skips the check while reading user constraints
            return instances

        group_block_instances = [const.instance_name.upper() for const in cls._validator_ctx().parent if isinstance(const, GroupBlocks)]
        for i0, i1 in itertools.pairwise(instances):
            if i0 not in group_block_instances and i1 not in group_block_instances:
                assert cls._validator_ctx().parent.parent.get_element(i0).parameters == \
                        cls._validator_ctx().parent.parent.get_element(i1).parameters, \
                        f"Parameters of {i0} and {i1} must match for SameTemplate in subckt {cls._validator_ctx().parent.parent.name}"
        return instances


class PlaceCloser(SoftConstraint):
    '''
        `instances` are preferred to be placed closer.
    '''
    instances: List[str]
    _inst_validator = types.validator('instances', allow_reuse=True)(validate_instances)

    def yield_constraints(self):
        yield DoNotIdentify(instances=self.instances)


class PlaceOnBoundary(SoftConstraint):
    '''
        Instances are placed on the specified boundary.
    '''
    north: Optional[List[str]]
    south: Optional[List[str]]
    east: Optional[List[str]]
    west: Optional[List[str]]
    northeast: Optional[str]
    northwest: Optional[str]
    southeast: Optional[str]
    southwest: Optional[str]

    @types.validator('north', 'south', 'east', 'west', 'northeast', 'northwest', 'southeast', 'southwest', allow_reuse=True)
    def instance_validator(cls, value):
        if isinstance(value, list):
            return validate_instances(cls, value)
        else:
            return validate_instances(cls, [value])

    def instances_on(cls, lst):
        sublist = list()
        for attr in lst:
            if value := getattr(cls, attr, False):
                if isinstance(value, list):
                    sublist.extend(value)
                else:
                    sublist.append(value)
        return sublist

    def yield_constraints(self):
        instances = self.instances_on(['north', 'south', 'east', 'west', 'northeast', 'northwest', 'southeast', 'southwest'])
        yield DoNotIdentify(instances=instances)


class PowerPorts(SoftConstraint):
    '''
    Defines power ports for each hieararchy

    Args:
        ports (list[str]): List of :obj:`ports`.
            The first port of top hierarchy will be used for power grid creation.
            Power ports are used to identify source and drain of transistors
            by identifying the terminal at higher potential.

    Example: ::

        {
            "constraint":"PowerPorts",
            "ports": ["VDD", "VDD1"],
        }
    '''
    ports: List[str]

    _upper_case = types.validator('ports', allow_reuse=True)(upper_case)
    _ports = types.validator('ports', allow_reuse=True)(validate_ports)


class GroundPorts(SoftConstraint):
    '''
    Ground port for each hieararchy

    Args:
        ports (list[str]): List of :obj:`ports`.
            The first port of top hierarchy will be used for ground grid creation.
            Power ports are used to identify source and drain of transistors
            by identifying the terminal at higher potential.

    Example: ::

        {
            "constraint": "GroundPorts",
            "ports": ["GND", "GNVD1"],
        }
    '''
    ports: List[str]

    _upper_case = types.validator('ports', allow_reuse=True)(upper_case)
    _ports = types.validator('ports', allow_reuse=True)(validate_ports)


class ClockPorts(SoftConstraint):
    '''
    Clock port for each hieararchy. These are used as stop-points
    during auto-constraint identification, means no constraint search
    will be done beyond the nets connected to these ports.

    Args:
        ports (list[str]): List of :obj:`ports`.

    Example: ::

        {
            "constraint": "ClockPorts",
            "ports": ["CLK1", "CLK2"],
        }
    '''
    ports: List[str]

    _upper_case = types.validator('ports', allow_reuse=True)(upper_case)


class DoNotUseLib(SoftConstraint):
    '''
    Primitive libraries which should not be used during hierarchy annotation.

    Args:
        libraries (list[str]): List of :obj:`libraries`.
        propagate: Copy this constraint to sub-hierarchies

    Example: ::

        {
            "constraint": "DoNotUseLib",
            "libraries": ["DP_NMOS", "INV"],
            "propagate": false
        }
    '''
    libraries: List[str]
    propagate: bool = False


class ConfigureCompiler(SoftConstraint):
    '''
    Compiler default optimization flags

    Args:
        is_digital(bool): true/false , stops any annotation or constraint generation
        auto_constraint(bool): true/false , stops auto-symmetry-constraint identification
        identify_array(bool): true/false , stops array identification
        fix_source_drain(bool): true/false , ensures (drain of NMOS/ source of PMOS) is at higher potential.
        remove_dummy_hierarchies(bool): true/false , Removes any single instance hierarchies.
        remove_dummy_devices(bool): true/false , Removes dummy devices in the design.
        merge_series_devices(bool): true/false , stack series devices
        merge_parallel_devices(bool): true/false , merge parallel devices
        propagate(bool): true/false , propagates these constarints to lower hierarchies

    Example: ::

        {
            "constraint": "ConfigureCompiler",
            "is_digital": true,
            "remove_dummy_hierarchies": true,
            "propagate": true
        }
    '''
    is_digital: bool = False  # Annotation and auto-constraint generation
    auto_constraint: bool = True  # Auto-constraint generation
    identify_array: bool = True  # Forbids/Allow any array identification
    fix_source_drain: bool = True  # Auto correction of source/drain terminals of transistors.
    remove_dummy_hierarchies: bool = True  # Removes any single instance hierarchies.
    remove_dummy_devices: bool = True  # Removes dummy transistors
    merge_series_devices: bool = True  # Merge series/stacked MOS/RES/CAP
    merge_parallel_devices: bool = True  # Merge parallel devices
    same_template: bool = True  # generates identical layouts for all existing hierarchies in the input netlist
    propagate: bool = True  # propagate constraint to all lower hierarchies


class Generator(SoftConstraint):
    '''
    Used to guide primitive generator.
    Args:
        name(str): name of genrator e.g., mos/cap/res/ring
        parameters(dict): {
                            pattern (str): common centroid (cc)/ Inter digitated (id)/Non common centroid (ncc)
                            shared_diff (bool): true/false
                            body (bool): true/ false
                            height (int): max height/nfin of a unit cell (including 16 dummy fins)
                            parallel_wires: {"net1":2, "net2":2} #to be implemented
                            }

    Example: ::

        {
            "constraint": "Generator",
            "name": "mos",
            "parameters : {
                            "pattern": "cc",
                            "parallel_wires": {"net1":2, "net2":2},
                            "body": true
                            }
        }
    '''
    name: Optional[str]
    parameters: Optional[dict]


class DoNotIdentify(SoftConstraint):
    '''
    Stop any auto-grouping of provided instances
    Automatically adds instances from all constraint

    WARNING: user-defined `groupblock`/`groupcap` constraint will ignore this constraint
    '''
    instances: List[str]
    _instance_attribute: str = "instances"

    @types.validator('instances', allow_reuse=True, always=True)
    def _check_instance(cls, value):
        return value


class SymmetricBlocks(HardConstraint):
    """SymmetricBlocks

    Defines a symmetry constraint between single and/or pairs of blocks.

    Args:
        pairs (list[list[str]]): List of pair of instances.
            A pair can have one :obj:`instance` or two instances,
            where single instance implies self-symmetry
        direction (str) : Direction for axis of symmetry. Literal::

            ['V', 'H']

    .. image:: ../images/SymmetricBlocks.PNG
        :align: center

    Example: ::

        {
            "constraint" : "SymmetricBlocks",
            "pairs" : [["MN0","MN1"], ["MN2","MN3"], ["MN4"]],
            "direction" : "V"
        }

    """
    pairs: List[List[str]]
    direction: Literal['H', 'V']
    _instance_attribute: str = "pairs"

    @types.validator('pairs', allow_reuse=True)
    def pairs_validator(cls, value):
        _ = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        if len(value) == 1:
            assert len(value[0]) == 2, 'Must contain at least a pair of two instances or more than two pairs.'
        for pair in value:
            assert len(pair) >= 1, 'Must contain at least one instance'
            assert len(pair) <= 2, 'Must contain at most two instances'
        value = [validate_instances(cls, pair) for pair in value]
        if not hasattr(cls._validator_ctx().parent.parent, 'elements'):
            # PnR stage VerilogJsonModule
            return value
        if len(cls._validator_ctx().parent.parent.elements) == 0:
            # skips the check while reading user constraints
            return value
        group_block_instances = [const.instance_name.upper() for const in cls._validator_ctx().parent if isinstance(const, GroupBlocks)]
        for pair in value:
            # logger.debug(f"pairs {self.pairs} {self.parent.parent.get_element(pair[0])}")
            if len([ele for ele in pair if ele in group_block_instances]) > 0:
                # Skip check for group block elements as they are added later in the flow
                continue
            elif len(pair) == 2:
                assert cls._validator_ctx().parent.parent.get_element(pair[0]), f"element {pair[0]} not found in design"
                assert cls._validator_ctx().parent.parent.get_element(pair[1]), f"element {pair[1]} not found in design"
                assert cls._validator_ctx().parent.parent.get_element(pair[0]).parameters == \
                    cls._validator_ctx().parent.parent.get_element(pair[1]).parameters, \
                    f"Parameters of the symmetry pair {pair} do not match in subckt {cls._validator_ctx().parent.parent.name}"
        return value

    def translate(cls, solver):

        def construct_expression(b1, b2=None):
            c = 'x' if cls.direction == 'V' else 'y'
            expression = getattr(b1, f'll{c}') + getattr(b1, f'ur{c}')
            if b2:
                expression += getattr(b2, f'll{c}') + getattr(b2, f'ur{c}')
            else:
                expression += getattr(b1, f'll{c}') + getattr(b1, f'ur{c}')
            return expression

        for i, instances in enumerate(cls.pairs):
            if len(instances) == 2:
                b0 = solver.bbox_vars(instances[0])
                b1 = solver.bbox_vars(instances[1])

                # the difference between the center lines should be <= 1/4th of the block heights
                # abs(cl_1 - cl_2) <= height_1/4  && abs(cl_1 - cl_2) <= height_2/4
                # abs(4.cl_1 - 4.cl_2) <= height_1, height_2
                c = 'y' if cls.direction == 'V' else 'x'
                b0_quad_cl = 2*(getattr(b0, f'll{c}') + getattr(b0, f'ur{c}'))
                b1_quad_cl = 2*(getattr(b1, f'll{c}') + getattr(b1, f'ur{c}'))
                expression = solver.And(
                    solver.Abs(b0_quad_cl - b1_quad_cl) <= getattr(b0, f'ur{c}') - getattr(b0, f'll{c}'),
                    solver.Abs(b0_quad_cl - b1_quad_cl) <= getattr(b1, f'ur{c}') - getattr(b1, f'll{c}'),
                )
                yield expression

            # center lines of pairs should match along the direction
            if i == 0:
                reference = construct_expression(*solver.iter_bbox_vars(instances))
            else:
                centerline = construct_expression(*solver.iter_bbox_vars(instances))
                expression = (reference == centerline)
                yield expression

    def yield_constraints(cls):
        instances = list()
        [instances.extend(pair) for pair in cls.pairs]
        yield DoNotIdentify(instances=instances)


class OffsetsScalings(BaseModel):
    offsets: List[int] = Field(default_factory=lambda: [0])
    scalings: List[Literal[-1, 1]] = Field(default_factory=lambda: [1])


class PlaceOnGrid(SoftConstraint):
    direction: Literal['H', 'V']
    pitch: int
    ored_terms: List[OffsetsScalings] = Field(default_factory=lambda: [OffsetsScalings()])

    @types.validator('ored_terms', allow_reuse=False)
    def ored_terms_validator(cls, value, values):
        pitch = values['pitch']
        for term in value:
            for offset in getattr(term, 'offsets'):
                assert 0 <= offset < pitch, f'offset {offset} should be less than pitch {pitch}'
        return value


class BlockDistance(SoftConstraint):
    '''
    Places the instances with a fixed gap.
    Also used in situations when routing is congested.

    Args:
        abs_distance (int) : Distance between two blocks.
            The number should be multiple of pitch of
            lowest horizontal and vertical routing layer i.e., M2 and M1

    .. image:: ../images/HorizontalDistance.PNG
        :align: center

    Example: ::

        {
            "constraint" : "BlockDistance",
            "abs_distance" : 420
        }
    '''
    abs_distance: int


class VerticalDistance(SoftConstraint):
    '''
    Places the instances with a fixed vertical gap.
    Also used in situations when routing is congested.

    Args:
        abs_distance (int) : Distance between two blocks.
            The number should be multiple of pitch of
            lowest horizontal routing layer i.e., M2

    .. image:: ../images/VerticalDistance.PNG
        :align: center

    Example: ::

        {
            "constraint" : "VerticalDistance",
            "abs_distance" : 84
        }

    '''
    abs_distance: int


class HorizontalDistance(SoftConstraint):
    '''
    Places the instances with a fixed horizontal gap.
    Also used in situations when routing is congested.

    Args:
        abs_distance (int) : Distance between two blocks.
            The number should be multiple of pitch of
            lowest vertical routing layer i.e., M1

    .. image:: ../images/HorizontalDistance.PNG
        :align: center

    Example: ::

        {
            "constraint" : "HorizontalDistance",
            "abs_distance" : 80
        }

    '''
    abs_distance: int


class GuardRing(SoftConstraint):
    '''
    Adds guard ring for particular hierarchy.

    Args:
        guard_ring_primitives (str) : Places this instance across boundary of a hierarchy
        global_pin (str): connect the pin of guard ring to this pin, mostly ground pin
        block_name: Name of the hierarchy

    Example: ::

        {
            "constraint" : "GuardRing",
            "guard_ring_primitives" : "guard_ring",
            "global_pin
        }
    '''
    guard_ring_primitives: str
    global_pin: str
    block_name: str


class GroupCaps(SoftConstraint):
    '''GroupCaps
    Creates a common centroid cap using a combination
    of unit sized caps. It can be of multiple caps.

    Args:
        name (str): name for grouped caps
        instances (List[str]): list of cap :obj:`instances`
        unit_cap (str): Capacitance value in fF
        num_units (List[int]): Number of units for each capacitance instance
        dummy (bool):  Whether to fill in dummies or not

   Example: ::

        {
            "constraint" : "GroupCaps",
            "name" : "cap_group1",
            "instances" : ["C0", "C1", "C2"],
            "num_units" : [2, 4, 8],
            "dummy" : true
        }
    '''
    name: str  # subcircuit name
    instances: List[str]
    unit_cap: str  # cap value in fF
    num_units: List
    dummy: bool  # whether to fill in dummies


class NetPriority(SoftConstraint):
    """
    Specify a non-negative priority for a list of nets for placement (default = 1).
    Example: {"constraint": "NetPriority", "nets": ["en", "enb"], "priority": 0}
    """
    nets: List[str]
    weight: int

    _weight = types.validator('weight', allow_reuse=True)(assert_non_negative)
    _upper_case = types.validator('nets', allow_reuse=True)(upper_case)


class NetConst(SoftConstraint):
    """NetConst

    Net based constraint. Shielding and critically can be defined.

    Args:
        nets (List[str]) : List of net names.
        shield (str, optional) : Name of net for shielding.
        criticality (int, optional) : Criticality of net.
            Higher criticality means the net would be routed first.

    Example: ::

        {
            "constraint" : "NetConst",
            "nets" : ["net1", "net2", "net3"],
            "shield" : "VSS",
            "criticality" : 10
        }
    """
    nets: List[str]
    shield: Optional[str]
    criticality: Optional[int]


class PortLocation(SoftConstraint):
    '''PortLocation
    Defines approximate location of the port.
    T (top), L (left), C (center), R (right), B (bottom)

    Args:
        ports (List[str]) : List of ports
        location (str): Literal::

            ['TL', 'TC', 'TR',
            'RT', 'RC', 'RB',
            'BL', 'BC', 'BR',
            'LB', 'LC', 'LT']

    Example ::

        {
            "constraint" : "PortLocation",
            "ports" : ["P0", "P1", "P2"],
            "location" : "TL"
        }
    '''
    ports: List
    location: Literal['TL', 'TC', 'TR',
                      'RT', 'RC', 'RB',
                      'BL', 'BC', 'BR',
                      'LB', 'LC', 'LT']


class SymmetricNets(SoftConstraint):
    '''SymmetricNets
    Defines two nets as symmetric.
    A symmetric net will also enforce a SymmetricBlock between blocks
    connected to the nets.

    Args:
        net1 (str) : Name on net1
        net2 (str) : Name of net2
        pins1 (List, Optional) : oredered list of connected pins to be matched
        pins2 (List, Optional) : oredered list of connected pins to be matched
        direction (str) : Literal ['H', 'V'], Horizontal or vertical line of symmetry

    Example ::

        {
            "constraint" : "SymmetricNets",
            "net1" : "net1"
            "net2" : "net2"
            "pins1" : ["block1/A", "block2/A", "port1"]
            "pins2" : ["block1/B", "block2/B", "port2"]
            "direction" : 'V'
        }
     '''

    net1: str
    net2: str
    pins1: Optional[List]
    pins2: Optional[List]
    direction: Literal['H', 'V']

    # TODO check net names
    _upper_case_net1 = types.validator('net1', allow_reuse=True)(upper_case_str)
    _upper_case_net2 = types.validator('net2', allow_reuse=True)(upper_case_str)

    @types.validator('pins1', allow_reuse=True)
    def pins1_validator(cls, pins1):
        instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        if pins1:
            pins1 = [pin.upper() for pin in pins1]
            for pin in pins1:
                if '/' in pin:
                    assert pin.split('/')[0].upper() in instances, f"element of pin {pin} not found in design"
                else:
                    validate_ports(cls, [pin])
        return pins1

    @types.validator('pins2', allow_reuse=True)
    def pins2_validator(cls, pins2, values):
        instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        if pins2:
            pins2 = [pin.upper() for pin in pins2]
            for pin in pins2:
                if '/' in pin:
                    assert pin.split('/')[0].upper() in instances, f"element of pin {pin} not found in design"
                else:
                    validate_ports(cls, [pin])
            assert len(values['pins1']) == len(pins2), "pin size mismatch"
        return pins2


class ChargeFlow(SoftConstraint):
    '''ChargeFlow
    Defines the current flowing through each pin.
    The chargeflow constraints help in improving the placement.

    Args:
        dist_type (str) : 'Euclidean' or 'Manhattan' distance between pins,
        time (list) : List of time intervals
        pin_current (dict) : current for each pin at different time intervals
    Example ::

        {
            "constraint" : "ChargeFlow",
            "dist_type" : [0,1.2,2.4],
            "time" : [0,1.2,2.4],
            "pin_current" : {"block1/A": [0,3.2,4.5], "block2/A":[2.3, 1.2,3.2]}
        }
     '''

    dist_type: Optional[Literal['Euclidean', 'Manhattan']] = 'Manhattan'
    time: List[float]
    pin_current: dict

    @types.validator('dist_type', allow_reuse=True)
    def dist_type_validator(cls, value):
        assert value == 'Manhattan' or value == 'Euclidean', 'dist_type must be either Euclidean or Manhattan'
        return value

    @types.validator('time', allow_reuse=True)
    def time_list_validator(cls, value):
        assert len(value) >= 1, 'Must contain at least one time stamp'
        return value

    # TODO add pin validators
    @types.validator('pin_current', allow_reuse=True)
    def pairs_validator(cls, pin_current, values):
        instances = get_instances_from_hacked_dataclasses(cls._validator_ctx())
        for pin, current in pin_current.items():
            assert pin.split('/')[0].upper() in instances, f"element {pin} not found in design"
            assert len(current) == len(values['time']), 'Must contain at least one instance'
        return pin_current


class MultiConnection(SoftConstraint):
    '''MultiConnection
    Defines multiple parallel wires for a net.
    This constraint is used to reduce parasitics and
    Electro-migration (EM) violations

    Args:
        nets (List[str]) : List of nets
        multiplier (int): Number of parallel wires

    Example ::

        {
            "constraint" : "MultiConnection",
            "nets" : ["N1", "N2", "N3"],
            "multiplier" : 4
        }
    '''
    nets: List[str]
    multiplier: int


class DoNotRoute(SoftConstraint):
    nets: List[str]

    _upper_case = types.validator('nets', allow_reuse=True)(upper_case)


class CustomizeRoute(BaseModel):
    nets: List[str]
    min_layer: Optional[str]
    max_layer: Optional[str]
    shield: bool = False
    match: bool = False


class Route(SoftConstraint):
    min_layer: Optional[str]
    max_layer: Optional[str]
    customize: List[CustomizeRoute] = []


class GroupBlocks(HardConstraint):
    """GroupBlocks

    Forces a hierarchy creation for group of instances.
    This brings the instances closer.
    This reduces the problem statement for placer thus providing
    better solutions.

    Args:
      instances (list[str]): List of :obj:`instances`
      template_name (str): Optional template name for the group (virtual hiearchy).
      instance_name (str): Instance name for the group (should start with X and unique in a subcircuit).
      generator (dict): adds a generator constraint to the created groupblock, look into the generator constraint for more options

    Example: ::

        {
            "constraint":"GroupBlocks",
            "instance_name": "X_MN0_MN1_MN3",
            "instances": ["MN0", "MN1", "MN3"]
            "generator": {name: 'MOS',
                        'parameters':
                            {
                            "pattern": "cc",
                            }
                        }
            "template_name": "DP1"
        }

    Note: If not provided a unique template name will be auto generated.
    Template_names are added with a post_script during the flow using a UUID based on
    all grouped instance parameters to create unique subcircuit names e.g., DP1_987654.
    """
    instance_name: str
    instances: List[str]
    template_name: Optional[str]
    generator: Optional[dict]
    constraints: Optional[List[Union[
        Align,
        Order,
        AlignInOrder,
        Floorplan,
        SymmetricBlocks,
        DoNotIdentify,
        SameTemplate,
        ConfigureCompiler]]] = None

    @types.validator('instance_name', allow_reuse=True)
    def group_block_name(cls, value):
        assert value, 'Cannot be an empty string'
        assert value.upper().startswith('X'), f"instance name {value} of the group should start with X"
        return value.upper()

    def translate(self, solver):
        # Non-zero width / height
        instances = get_instances_from_hacked_dataclasses(self)
        bb = solver.bbox_vars(self.instance_name)
        yield bb.llx < bb.urx
        yield bb.lly < bb.ury
        # Grouping into common bbox
        for b in solver.iter_bbox_vars((x for x in self.instances if x in instances)):
            yield b.urx <= bb.urx
            yield b.llx >= bb.llx
            yield b.ury <= bb.ury
            yield b.lly >= bb.lly
        for b in solver.iter_bbox_vars((x for x in instances if x not in self.instances)):
            yield solver.Or(
                b.urx <= bb.llx,
                bb.urx <= b.llx,
                b.ury <= bb.lly,
                bb.ury <= b.lly,
            )


ConstraintType = Union[
    # ALIGN Internal DSL
    Order, Align, Floorplan, Spread,
    AssignBboxVariables,
    AspectRatio,
    Boundary,
    # Additional User constraints
    AlignInOrder,
    # Legacy Align constraints
    # (SoftConstraints)
    CompactPlacement,
    Generator,
    SameTemplate,
    GroupBlocks,
    PlaceCloser,
    PlaceOnBoundary,
    DoNotIdentify,
    PlaceOnGrid,
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
    DoNotRoute,
    # Setup constraints
    PowerPorts,
    GroundPorts,
    ClockPorts,
    DoNotUseLib,
    ConfigureCompiler,
    NetPriority,
    Route,
    ChargeFlow
]


class ConstraintDB(types.List[ConstraintType]):

    @types.validate_arguments
    def append(self, constraint: ConstraintType):
        if (constraint_str := repr(constraint)) not in self._cache:
            if hasattr(constraint, 'translate'):
                if self.parent._checker is None:
                    self.parent.verify()
                self.parent.verify(constraint=constraint)
            super().append(constraint)
            self._cache.add(constraint_str)
        else:
            logger.debug(f"Constraint is duplicated: {constraint_str}")

    @types.validate_arguments
    def remove(self, constraint: ConstraintType):
        super().remove(constraint)

    def __init__(self, *args, **kwargs):
        super().__init__()
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
        # TODO: Shouldn't need to invalidate this
        #       Lots of thrash happening here
        self.parent._checker = None
        with set_context(self):
            for x in data:
                super().append(x)

    def checkpoint(self):
        if self.parent._checker is None:
            self.parent.verify()

        self.parent._checker.checkpoint()
        return super().checkpoint()

    def _revert(self):
        self.parent._checker.revert()
        super()._revert()


def expand_user_constraints(const_list):
    for const in const_list:
        if hasattr(const, 'yield_constraints'):
            logger.info(f'expanding: {const}')
            with types.set_context(const.parent):
                yield from const.yield_constraints()
        if not isinstance(const, UserConstraint):
            yield const
