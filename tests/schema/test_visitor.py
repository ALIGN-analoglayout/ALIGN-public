import pytest

from align.schema.types import BaseModel, Optional, List, Dict, String
from align.schema.visitor import Visitor, Transformer, cache

@pytest.fixture
def dummy():
    class DummyModel(BaseModel):
        arg1: String
        arg2: Optional[String]
        arg3: List[String]
        arg4: List[Optional[String]]
        arg5: Dict[String, String]
        arg6: Dict[String, Optional[String]]
        arg7: "Optional[DummyModel]"
        arg8: "Optional[List[DummyModel]]"
    DummyModel.update_forward_refs()

    base = DummyModel(
        arg1 = 'arg1',
        arg3 = ['arg3_1', 'arg3_2'],
        arg4 = [],
        arg5 = {'arg5_k': 'arg5_v'},
        arg6 = {'arg6_k': None}
    )
    dummy = DummyModel(
        arg1 = 'arg1',
        arg3 = ['arg3_1', 'arg3_2'],
        arg4 = [],
        arg5 = {'arg5_k': 'arg5_v'},
        arg6 = {'arg6_k': None},
        arg7 = base,
        arg8 = [base, base]
    )
    return dummy

def test_visitor_no_output(dummy):
    assert Visitor().visit(dummy) == []

def test_visitor_raw_output(dummy):

    class StrValVisitor(Visitor):
        def visit_String(self, node):
            return node

    assert StrValVisitor().visit(dummy) == [
        'arg1',
        'arg3_1',
        'arg3_2',
        'arg5_v',
        'arg1',
        'arg3_1',
        'arg3_2',
        'arg5_v',
        'arg1',
        'arg3_1',
        'arg3_2',
        'arg5_v',
        'arg1',
        'arg3_1',
        'arg3_2',
        'arg5_v',
    ]

def test_visitor_processed_output(dummy):

    class DummyCounter(Visitor):
        '''Simply counts the number of times the dummy class is encountered'''
        def visit_DummyModel(self, node):
            return sum(self.generic_visit(node)) + 1

    assert DummyCounter().visit(dummy) == 4

def test_transformer_no_visitor(dummy):
    assert Transformer().visit(dummy.arg1) is dummy.arg1
    assert Transformer().visit(dummy.arg2) is dummy.arg2
    assert Transformer().visit(dummy.arg3) is dummy.arg3
    assert Transformer().visit(dummy.arg4) is dummy.arg4
    assert Transformer().visit(dummy.arg5) is dummy.arg5
    assert Transformer().visit(dummy.arg6) is dummy.arg6
    assert Transformer().visit(dummy.arg7) is dummy.arg7
    assert Transformer().visit(dummy.arg8) is dummy.arg8
    assert Transformer().visit(dummy) is dummy

def test_transformer_string_visitor(dummy):

    class AddStringPrefix(Transformer):
        def visit_String(self, node):
            return 'prefix_' + node

    transformed = AddStringPrefix().visit(dummy)
    assert isinstance(transformed, dummy.__class__)
    # String in subtree
    assert transformed.arg1 == 'prefix_arg1'
    assert transformed.arg1 is not dummy.arg1
    # No string in subtree
    assert transformed.arg2 == None
    assert transformed.arg2 is dummy.arg2
    # String in subtree
    assert transformed.arg3 == ['prefix_arg3_1', 'prefix_arg3_2']
    assert transformed.arg3 is not dummy.arg3
    # No string in subtree
    assert transformed.arg4 == []
    assert transformed.arg4 is dummy.arg4, f'old:({id(dummy.arg4)}, {dummy.arg4}), new:({id(transformed.arg4)}, {transformed.arg4})'
    # String in subtree
    assert transformed.arg5 == {'arg5_k': 'prefix_arg5_v'}
    assert transformed.arg5 is not dummy.arg5
    # No string in subtree
    assert transformed.arg6 == {'arg6_k': None}
    assert transformed.arg6 is dummy.arg6
    # Expected result for arg7 and arg8
    basedict = {'arg1': 'prefix_arg1',
                'arg2': None,
                'arg3': ['prefix_arg3_1',
                        'prefix_arg3_2'],
                'arg4': [],
                'arg5': {'arg5_k': 'prefix_arg5_v'},
                'arg6': {'arg6_k': None},
                'arg7': None,
                'arg8': None}
    # String in subtree
    assert transformed.arg7 == basedict
    assert transformed.arg7 is not dummy.arg7
    # String in subtree
    assert transformed.arg8 == [basedict, basedict]
    assert transformed.arg8 is not dummy.arg8
    # Ensure cache is working for generic_visitor
    assert transformed.arg7 is transformed.arg8[0]
    assert transformed.arg8[0] is transformed.arg8[1]

def test_cache(dummy):

    class UncachedTransformer(Transformer):
        def visit_DummyModel(self, node):
            if not hasattr(self, 'top'):
                self.top = node
                return self.generic_visit(node)
            else:
                return node.copy()
    control = UncachedTransformer().visit(dummy)
    assert control.arg7 is not control.arg8[0]
    assert control.arg8[0] is not control.arg8[1]

    class CachedTransformer(Transformer):
        @cache # DO THIS FOR MOST VISITORS
        def visit_DummyModel(self, node):
            if not hasattr(self, 'top'):
                self.top = node
                return self.generic_visit(node)
            else:
                return node.copy()
    transformed = CachedTransformer().visit(dummy)
    assert transformed.arg7 is transformed.arg8[0]
    assert transformed.arg8[0] is transformed.arg8[1]
