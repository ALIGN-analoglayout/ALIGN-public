import abc
import logging

logger = logging.getLogger(__name__)

from . import schema
from .types import List, Dict

class Visitor(object):
    """
    The Visitor base class walks the ALIGN specification tree and calls a
    visitor function for every node found.  This is very similar to the
    `NodeVisitor` class implemented by the python internal `ast` module (except
    that it operates on schema.BaseModel derivates).

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
    def visit(self, node):
        if isinstance(node, (schema.BaseModel, List, Dict, str, int, type(None))):
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

    def generic_visit(self, node):
        if isinstance(node, schema.BaseModel):
            return self.flatten(self.visit(v) for _, v in self.iter_fields(node))
        elif isinstance(node, (str, int, type(None))):
            return None
        elif isinstance(node, List):
            return self.flatten(self.visit(v) for v in node)
        elif isinstance(node, Dict):
            return self.flatten(self.visit(v) for _, v in node.items())
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

    def generic_visit(self, node):
        if isinstance(node, schema.BaseModel):
            field_dict = dict(self.iter_fields(node))
            new_field_dict = {k: self.visit(v) for k, v in field_dict.items()}
            return node if all(x is y for x, y in zip(field_dict.values(), new_field_dict.values())) else node.__class__(**new_field_dict)
        elif isinstance(node, (int, str, type(None))):
            return node
        elif isinstance(node, List):
            new_node = [self.visit(v) for v in node]
            return node if all(x is y for x, y in zip(node, new_node)) else new_node
        elif isinstance(node, Dict):
            new_node = {k: self.visit(v) for k, v in node.items()}
            return node if all(x is y for x, y in zip(node.values(), new_node.values())) else new_node
        else:
            raise NotImplementedError( \
                f'{self.__class__.__name__}.generic_visit() does not support node of type {node.__class__.__name__}:\n{node}')
