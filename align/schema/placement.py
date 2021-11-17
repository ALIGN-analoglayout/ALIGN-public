from pydantic import Field
from .types import BaseModel, List, Literal


class OffsetsScalings(BaseModel):
    offsets: List[int] = Field(default_factory=lambda: [0])
    scalings: List[Literal[-1, 1]] = Field(default_factory=lambda: [1])

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)


class PlacementGrid(BaseModel):
    direction: Literal['H', 'V']
    pitch: int
    ored_terms: List[OffsetsScalings] = Field(default_factory=lambda: [OffsetsScalings()])
