from .types import BaseModel, List, NamedTuple

class Rect(BaseModel):
    llx: int
    lly: int
    urx: int
    ury: int

class Transformation(BaseModel):
    oX: int # Offset
    oY: int
    sX: int # Scale Factor
    sY: int

class Terminal(BaseModel):
    name: str
    layer: str
    rect: Rect
    pin: Optional[str]

class Pin(BaseModel):
    name: str
    terminals: List[Terminal]

    @types.validator('terminals')
    def validate_connected(self, v, values):
        assert all(x.name == values['name'] for x in v)


class LayoutTemplate(BaseModel):
    bbox: Rect
    subinsts: "List[LayoutInstance]"
    global_routes: List[Terminal]
    terminals: List[Terminal]

class LayoutInstance(BaseModel):
    layout: LayoutDefinition
    transformation: Transformation

Layout.update_forward_refs()