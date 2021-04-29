import pytest

from align.schema.types import BaseModel, List, Dict


class BaseType(BaseModel):
    name: str


class CompositionalType(BaseModel):
    name: str
    child: BaseType
    children: List[BaseType]
    children_as_dict: Dict[str, BaseType]


def test_type_inference():
    myobj = CompositionalType(**{
        'name': 'toplevel',
        'child': {'name': 'orphanchild'},
        'children': [
            {'name': 'child1'},
            {'name': 'child2'}
        ],
        'children_as_dict': {
            'child1': {'name': 'child1'},
            'child2': {'name': 'child2'},
        }
    })
    assert isinstance(myobj, CompositionalType)
    assert isinstance(myobj.child, BaseType)
    assert isinstance(myobj.children, List)
    assert isinstance(myobj.children_as_dict, Dict)
    assert all(isinstance(x, BaseType) for x in myobj.children)
    assert all(isinstance(x, str) for x in myobj.children_as_dict.keys())
    assert all(isinstance(x, BaseType) for x in myobj.children_as_dict.values())

def test_type_relationships():
    myobj = CompositionalType(
        name='toplevel',
        child={'name': 'orphanchild'},
        children=[
            {'name': 'child1'},
            {'name': 'child2'}
        ],
        children_as_dict={
            'child1': {'name': 'child1'},
            'child2': {'name': 'child2'},
        }
    )
    assert myobj.parent is None, id(myobj.parent)
    assert myobj.child.parent == myobj
    assert len(myobj.children) == 2
    child1, child2 = myobj.children
    assert child1.parent == child2.parent
    assert child1.parent.parent == myobj
    assert len(myobj.children_as_dict) == 2
    assert myobj.children_as_dict['child1'].parent == myobj.children_as_dict['child2'].parent
    assert myobj.children_as_dict['child1'].parent.parent == myobj
