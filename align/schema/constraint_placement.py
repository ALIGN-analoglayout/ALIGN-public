from .types import Union, Optional, Literal, List
from .constraint import PlacementConstraint
from pydantic import validator


class Alignment(PlacementConstraint):
    constraint_name: Literal["alignment"]
    instances: List[str]
    direction: Optional[Literal['horizontal', 'vertical']] = 'horizontal'
    edge: Optional[Literal['top', 'center', 'bottom', 'left', 'right']] = 'bottom'
    abut: Optional[bool] = True

    @classmethod
    @validator('edge')
    def _validate_edge(cls, v, values):
        if v == 'horizontal':
            assert v in ["top", "bottom", "center"], f'edge should be top, bottom or center'
        else:
            assert v in ["left", "right", "center"], f'edge should be left, right or center'

    def check(self):
        pass


class Generator(PlacementConstraint):
    constraint_name: Literal["generator"]
    instances: List[str]
    style: Optional[Literal['cc', 'id']] = 'cc'
    alias: Optional[str]
    n_rows: Optional[int] = None
    add_guard_ring: Optional[bool] = False

    def check(self):
        pass


class Orientation(PlacementConstraint):
    constraint_name: Literal["orientation"]
    instances: List[str]
    flip_x: Optional[bool] = False
    flip_y: Optional[bool] = False

    def check(self):
        pass


class Boundary(PlacementConstraint):
    constraint_name: Literal["boundary"]
    subcircuits: List[str]
    height_min: Optional[float] = None
    height_max: Optional[float] = None
    aspect_ratio_min: Optional[float] = None
    aspect_ratio_max: Optional[float] = None

    @classmethod
    @validator('height_max', 'height_min', 'aspect_ratio_min', 'aspect_ratio_max')
    def _validate_nonzero(cls, v):
        assert v > 0, f'Value {v} should be positive.'

    @classmethod
    @validator('height_max')
    def _validate_height(cls, v, values):
        if values['height_min'] is not None:
            v2 = values['height_min']
            assert v > v2, f'Value {v} should be greater than lower bound {v2}.'
    
    @classmethod
    @validator('aspect_ratio_max')
    def _validate_aspect_ratio(cls, v, values):
        if values['aspect_ratio_min'] is not None:
            v2 = values['aspect_ratio_min']
            assert v > v2, f'Value {v} should be greater than lower bound {v2}.'

    def check(self):
        pass


class ConstraintsPlacement(PlacementConstraint):
    constraints: List[Union[Alignment, Generator, Orientation, Boundary]]

    def check(self):
        pass

# TODO: Enhance PlacementConstraint to handle list of lists (e.g. symmetry)
