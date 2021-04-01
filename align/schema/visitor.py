import abc
import logging
import functools

logger = logging.getLogger(__name__)

from . import types

def cache(function=None, *, types=None):
    '''
    This decorator will store the results of a visitor method
    in self.cache and retrieve it if the id of a new object
    matches one in the cache.

    This simultaeneously helps avoid redundant computation and
    ensures that shared pointers in the original tree results
    in shared pointers in the new tree. If this is not desired
    (if the result of a subtree is dependent upon the nodes
    above it for example), please implement a custom visit_*
    method WITHOUT the @cache decorator.

    It is to be noted that the decorator can be used in two ways:
    1) @cache
       Cache all results (Used 99.999% of the time)
    2) @cache(types=[...])
       Cache all incoming nodes that are instances of types
       (Mostly used by generic_visit)
    '''
    def decorator(f):
        @functools.wraps(f)
        def cached_method(visitor, node):
            if types and not isinstance(node, types):
                return f(visitor, node)
            try:
                return visitor.cache[id(node)]
            except:
                pass
            newnode = f(visitor, node)
            visitor.cache[id(node)] = newnode
            return newnode
        return cached_method
    if function:
        return decorator(function)
    else:
        return decorator

class Visitor(object):
    """
    The Visitor base class walks the ALIGN specification tree and calls a
    visitor function for every node found.  This is very similar to the
    `NodeVisitor` class implemented by the python internal `ast` module (except
    that it operates on types.BaseModel derivates).

    This class is meant to be subclassed, with the subclass adding visitor
    methods. The visitor functions for the nodes are ``'visit_'`` + the
    class name of the node.  So a `SubCircuit` node visit function would
    be `visit_SubCircuit`. If no visitor function exists for a node the
    `generic_visit` visitor is used instead.

    Don't use the `Visitor` if you want to apply changes to nodes during
    traversing.  For this a special visitor exists (`NodeTransformer`) that
    allows modifications.

    Usually you use the Visitor like this::
    result = YourVisitor().visit(node)

    Where the type of result is determined by the return type of the
    root node visitor. Note that the generic_visitor attempts to return
    either a list or None for most visitors.
    """

    def __init__(self):
        self.cache = {}

    def visit(self, node):
        if isinstance(node, (types.BaseModel, types.List, types.Dict, str, int, type(None))):
            method = 'visit_' + node.__class__.__name__
            return getattr(self, method, self.generic_visit)(node)
        else:
            raise NotImplementedError(f'{self.__class__.__name__}.visit() does not support node of type {node.__class__.__name__}:\n{node}')

    @staticmethod
    def iter_fields(node):
        for field in node.__fields__.keys():
            try:
                yield field, getattr(node, field)
            except:
                pass

    @staticmethod
    def flatten(l):
        ret = []
        for item in l:
            if isinstance(item, list):
                ret.extend(item)
            elif item is not None:
                ret.append(item)
        return ret

    @cache(types=(types.BaseModel, types.List, types.Dict))
    def generic_visit(self, node):
        if isinstance(node, types.BaseModel):
            return self.flatten(self.visit(v) for _, v in self.iter_fields(node))
        elif isinstance(node, types.List):
            return self.flatten(self.visit(v) for v in node)
        elif isinstance(node, types.Dict):
            return self.flatten(self.visit(v) for _, v in node.items())
        elif isinstance(node, (str, int, type(None))):
            return None
        else:
            raise NotImplementedError( \
                f'{self.__class__.__name__}.generic_visit() does not support node of type {node.__class__.__name__}:\n{node}')

class Transformer(Visitor):
    """
    An ALIGN `Visitor` subclass that walks the ALIGN specification tree and
    allows modification of nodes.

    By default, the Transformer will walk the AST and use the return value of
    visitor methods to replace the old node. Note that the return value may be
    the original node in which case no replacement takes place.

    Keep in mind that if the node you're operating on has child nodes you must
    either transform the child nodes yourself or call the `generic_visit`
    method for the node first.

    Usually you use the transformer like this::
    node = YourTransformer().visit(node)
    """

    @cache(types=(types.BaseModel, types.List, types.Dict))
    def generic_visit(self, node):
        if isinstance(node, types.BaseModel):
            field_dict = dict(self.iter_fields(node))
            new_field_dict = {k: self.visit(v) for k, v in field_dict.items()}
            return node if all(x is y for x, y in zip(field_dict.values(), new_field_dict.values())) else node.__class__(**new_field_dict)
        elif isinstance(node, types.List):
            new_node = [self.visit(v) for v in node]
            return node if all(x is y for x, y in zip(node, new_node)) else new_node
        elif isinstance(node, types.Dict):
            new_node = {k: self.visit(v) for k, v in node.items()}
            return node if all(x is y for x, y in zip(node.values(), new_node.values())) else new_node
        elif isinstance(node, (int, str, type(None))):
            return node
        else:
            raise NotImplementedError( \
                f'{self.__class__.__name__}.generic_visit() does not support node of type {node.__class__.__name__}:\n{node}')
