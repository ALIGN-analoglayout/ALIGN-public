import pytest

from align.schema.types import BaseModel, List, Dict


class BaseType(BaseModel):
    name: str


class CompositionalType(BaseModel):
    name: str
    child: BaseType
    children: List[BaseType]
    child_as_dict: Dict[str, BaseType]


def test_type_relationships():
    children = [
        BaseType(name='child1'),
        BaseType(name='child2')
    ]
    myobj = CompositionalType(
        name='toplevel',
        child=children[0].copy(),
        children=children,
        child_as_dict={x.name: x.copy() for x in children}
    )
    assert myobj.parent is None
    assert myobj.child.parent == myobj
    assert len(myobj.children) == 2
    child1, child2 = myobj.children
    assert child1.parent == child2.parent
    assert child1.parent.parent == myobj
    assert len(myobj.child_as_dict) == 2
    assert myobj.child_as_dict['child1'].parent == myobj.child_as_dict['child2'].parent
    assert myobj.child_as_dict['child1'].parent.parent == myobj
