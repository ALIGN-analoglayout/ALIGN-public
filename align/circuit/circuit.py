import pathlib

from .netlist import Netlist
from .library import Library

class Settings(pydantic.BaseModel):
    pdkdir : pathlib.Path
    designdir : pathlib.Path
    workingdir : pathlib.Path
    outputdir: pathlib.Path

class Circuit(pydantic.BaseModel):
    pdk : PDK
    settings: Settings
    design : SubCircuit
    library : Library
    transformers: Dict[str, int] # Transformer : Iteration

    @property
    def name():
        return self.design.name