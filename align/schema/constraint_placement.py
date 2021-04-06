from .types import Union, Optional, Literal, List, Dict
from .constraint import ConstraintBase
from pydantic import validator, Field
import more_itertools as itertools

# Common validators
def normalize_direction(direction: str) -> str:
    return direction[0].upper()

def assert_nonnegative(v: int) -> int:
    assert v >=0
    return v

def assert_length_gt1(v: int) -> int:
    assert len(v) > 1
    return v

#######################################################################################################################
# TODO: Validate that instances exist in the subcircuit including virtual subcircuits defined by `generator` constraints
# TODO: Make sure instances do not overlap
#######################################################################################################################


class Align(ConstraintBase):
    '''
        Align `instances` in order, along the `direction`, on the `line`
        `direction` == horizontal => left to right
        `direction` == vertical   => top to bottom
    '''
    name: Literal['align']
    instances: List[str]
    direction: Literal['horizontal', 'vertical', 'h', 'v']
    line: Optional[Literal['bottom', 'top', 'left', 'right', 'center', ]] = 'bottom'
    abut: Optional[bool] = True
    order: Optional[bool] = True

    # validators
    _normalize_direction = validator('direction', allow_reuse=True)(normalize_direction)
    _assert_length_gt1 = validator('instances', allow_reuse=True)(assert_length_gt1)

    @classmethod
    @validator('line')
    def _validate_line(cls, v, values):
        if values['direction'] == 'H':
            assert v in ['bottom', 'center', 'top'], f'line should be bottom, center or top'
        else:
            assert v in ['left', 'center', 'right'], f'line should be left, center or right'
        return v

    def decompose(self):
        constraints = []
        if self.direction == 'H':
            constraints.append(AlignHorizontal(name='align_horizontal', instances=self.instances, line=self.line))
            if self.order:
                constraints.append(OrderHorizontal(name='order_horizontal', instances=self.instances, abut=self.abut))
        else:
            constraints.append(AlignVertical(name='align_vertical', instances=self.instances, line=self.line))
            if self.order:
                constraints.append(OrderVertical(name='order_vertical', instances=self.instances, abut=self.abut))
        assert len(constraints) > 0
        return constraints

    def check(self):
        pass


class AlignHorizontal(ConstraintBase):
    '''
        Align `instances` horizontally on the `line`
    '''
    name: Literal['align_horizontal']
    instances: List[str]
    line: Literal['bottom', 'top', 'center']

    # validators
    _assert_length_gt1 = validator('instances', allow_reuse=True)(assert_length_gt1)

    def serialize(self):
        return self.dict()
        
    def check(self):
        constraints = super().check()
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'bottom':
                constraints.append(b1.lly == b2.lly)
            elif self.line == 'top':
                constraints.append(b1.ury == b2.ury)
            else:
                constraints.append(b1.ury + b1.lly == b2.ury + b2.lly)
        return constraints


class AlignVertical(ConstraintBase):
    ''' 
        Align `instances` vertically on the `line` 
    '''    
    name: Literal['align_vertical']
    instances: List[str]
    line: Literal['left', 'center', 'right']

    # validators
    _assert_length_gt1 = validator('instances', allow_reuse=True)(assert_length_gt1)

    def serialize(self):
        return self.dict()

    def check(self):
        constraints = super().check()
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.line == 'left':
                constraints.append(b1.llx == b2.llx)
            elif self.line == 'right':
                constraints.append(b1.urx == b2.urx)
            else:
                constraints.append(b1.urx + b1.llx == b2.urx + b2.llx)
        return constraints


class OrderVertical(ConstraintBase):
    ''' 
        Order `instances` vertically bottom to top
    '''
    name: Literal['order_vertical']
    instances: List[str]
    abut: Optional[bool] = False

    # validators
    _assert_length_gt1 = validator('instances', allow_reuse=True)(assert_length_gt1)

    def serialize(self):
        return self.dict()

    def check(self):
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.abut:
                constraints.append(b1.ury == b2.lly)
            else:
                constraints.append(b1.ury <= b2.lly)
        return constraints


class OrderHorizontal(ConstraintBase):
    ''' 
        Order `instances` horizontally left to right
    '''
    name: Literal['order_horizontal']
    instances: List[str]
    abut: Optional[bool] = False

    # validators
    _assert_length_gt1 = validator('instances', allow_reuse=True)(assert_length_gt1)

    def serialize(self):
        return self.dict()

    def check(self):
        bvars = self._get_bbox_vars(self.instances)
        for b1, b2 in itertools.pairwise(bvars):
            if self.abut:
                constraints.append(b1.urx == b2.llx)
            else:
                constraints.append(b1.urx <= b2.llx)
        return constraints


class Generator(ConstraintBase):
    ''' 
        Place `instances` in a particular `style` 
    '''
    name: Literal['generator']
    instances: List[str]
    style: Optional[Literal['cc', 'id']] = 'cc'
    alias: Optional[str] = None
    params: Optional[Dict[str, Union[str, int]]] = Field(default_factory=lambda: {})

    def check(self):
        pass


class Mirror(ConstraintBase):
    ''' 
        Mirror `instances` along `x_axis` and/or `y_axis`
    '''
    name: Literal['mirror']
    instances: List[str]
    x_axis: Optional[bool] = False
    y_axis: Optional[bool] = False

    def check(self):
        pass


class Boundary(ConstraintBase):
    ''' 
        Define boundary for a subcircuit
        aspect_ratio = height / width
    '''
    name: Literal['boundary']
    aspect_ratio_min: Optional[float] = None
    aspect_ratio_max: Optional[float] = None
    height_max: Optional[int] = None
    width_max: Optional[int] = None

    # validators
    _assert_nonnegative = validator(
        'height_max', 'width_max', 'aspect_ratio_min', 'aspect_ratio_max',
        allow_reuse=True)(assert_nonnegative)
    
    @classmethod
    @validator('aspect_ratio_max')
    def _validate_aspect_ratio(cls, v, values):
        if values['aspect_ratio_min'] is not None:
            v2 = values['aspect_ratio_min']
            assert v > v2, f'Value {v} should be greater than {v2}.'

    def check(self):
        pass


class ConstraintsPlacement(ConstraintBase):
    
    constraints: List[Union[
        Align, AlignHorizontal, AlignVertical, OrderHorizontal, OrderVertical,
        Generator, Mirror, Boundary]]

    def check(self):
        pass
