import pydantic

from .library import library
from .subcircuit import SubCircuit

class Transformer(pydantic.BaseModel):
    library: Library
    subckt : SubCircuit
