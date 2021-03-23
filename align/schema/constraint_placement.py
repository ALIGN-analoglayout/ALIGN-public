from .types import Union, Optional, Literal, List
from .constraint import ConstraintBase
from pydantic import validator


class Alignment(ConstraintBase):
    constraint_name: Literal["alignment"]
    instances: List[str]
    direction: Optional[Literal['horizontal', 'vertical']] = 'horizontal'
    edge: Optional[Literal['top', 'center', 'bottom', 'left', 'right']] = 'bottom'

    @classmethod
    @validator('edge')
    def _validate_edge(cls, v, values):
        if v == 'horizontal':
            assert v in ["top", "bottom", "center"], f'edge should be top, bottom or center'
        else:
            assert v in ["left", "right", "center"], f'edge should be left, right or center'

    def check(self):
        pass


class Generator(ConstraintBase):
    constraint_name: Literal["generator"]
    instances: List[str]
    style: Optional[Literal['cc', 'id']] = 'cc'
    alias: Optional[str]
    n_rows: Optional[int] = None
    add_guard_ring: Optional[Literal[True, False]] = False

    def check(self):
        pass


class Orientation(ConstraintBase):
    constraint_name: Literal["orientation"]
    instances: List[str]
    flip_x: Optional[Literal[True, False]] = False
    flip_y: Optional[Literal[True, False]] = False

    def check(self):
        pass


class ConstraintsPlacement(ConstraintBase):
    constraints: List[Union[Alignment, Generator, Orientation]]

    def check(self):
        pass

# TODO: Enhance ConstraintBase to handle list of lists (e.g. symmetry)
