__all__ = [
    'BaseModel', 'List', 'Dict', 'SpiceStr',
    'validator', 'root_validator', 'validate_arguments',
    'Optional', 'Union',
    'NamedTuple', 'Literal',
    'ClassVar', 'PrivateAttr'
]
# Pass through directly from typing
from typing import \
    Optional, \
    Union, \
    NamedTuple, \
    ClassVar
try:
    # Python 3.8+
    from typing import Literal
except:
    # Python 3.7 Backport
    from typing_extensions import Literal

# Pass through directly from pydantic
from pydantic import \
    validator, \
    root_validator, \
    validate_arguments, \
    PrivateAttr

# Custom ALIGN types (BaseModel, List, Dict) defined below
import pydantic.generics
import typing
import collections
import random
import string
import contextvars
import contextlib

_ctx = contextvars.ContextVar('current_constructor', default=None)


@contextlib.contextmanager
def set_context(obj):
    token = _ctx.set(obj)
    try:
        yield
    finally:
        _ctx.reset(token)


def set_parent(item, parent):
    if isinstance(item, (BaseModel, List, Dict)):
        assert item._parent is None or item._parent == parent, f'Trying to reset parent for {item} from {item._parent} to {parent}'
        item._parent = parent


class BaseModel(pydantic.BaseModel):

    @property
    def parent(self):
        return self._parent

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        copy_on_model_validation = False

    def __init__(self, *args, **kwargs):
        self._parent = _ctx.get()
        with set_context(self):
            super().__init__(*args, **kwargs)

    def copy(self, include=None, exclude=None, update={}):
        def to_dict(val):
            if isinstance(val, list):
                return [to_dict(v) for v in val]
            elif isinstance(val, dict):
                return {to_dict(k): to_dict(v) for k, v in val.items()}
            elif isinstance(val, (BaseModel, Dict)):
                return val.dict(
                    exclude_unset=True,
                    exclude_defaults=True)
            elif isinstance(val, List):
                return val.dict(
                    exclude_unset=True,
                    exclude_defaults=True)['__root__']
            else:
                return val
        ctx = self.parent if _ctx.get() is None else _ctx.get()
        v = {
            **self.dict(
                exclude_unset=True,
                exclude_defaults=True,
                include=include,
                exclude=exclude),
            **{
                k: to_dict(v)
                for k, v
                in update.items()
            }
        }
        with set_context(ctx):
            return self.__class__(**v)

    @classmethod
    def _validator_ctx(cls):
        self = _ctx.get()
        assert self is not None, 'Could not retrieve ctx'
        return self

    _parent = pydantic.PrivateAttr()


KeyT = typing.TypeVar('KeyT')
DataT = typing.TypeVar('DataT')


class List(pydantic.generics.GenericModel, typing.Generic[DataT]):
    __root__: typing.Sequence[DataT]

    _commits = pydantic.PrivateAttr()
    _parent = pydantic.PrivateAttr()

    @property
    def parent(self):
        return self._parent

    class Config:
        validate_assignment = True
        extra = 'forbid'
        copy_on_model_validation = False
        allow_mutation = False

    def append(self, item: DataT):
        self.__root__.append(item)

    def extend(self, items: "List[DataT]"):
        for item in items:
            self.append(item)

    def remove(self, item: DataT):
        return self.__root__.remove(item)

    def pop(self, index=-1):
        return self.__root__.pop(index)

    def __len__(self):
        return len(self.__root__)

    def __iter__(self):
        return iter(self.__root__)

    def __getitem__(self, item):
        return self.__root__[item]

    def __setitem__(self, item, value):
        self.__root__[item] = value

    def __delitem__(self, sliceobj):
        del self.__root__[sliceobj]

    def __eq__(self, other):
        return self.__root__ == other

    def __init__(self, *args, **kwargs):
        if '__root__' not in kwargs:
            if len(args) == 1:
                kwargs['__root__'] = args[0]
                args = tuple()
            elif len(args) == 0:
                kwargs['__root__'] = []
        self._parent = _ctx.get()
        with set_context(self):
            super().__init__(*args, **kwargs)
        self._commits = collections.OrderedDict()

    def _gen_commit_id(self, nchar=8):
        id_ = ''.join(random.choices(
            string.ascii_uppercase + string.digits, k=nchar))
        return self._gen_commit_id(nchar) if id_ in self._commits else id_

    def checkpoint(self):
        self._commits[self._gen_commit_id()] = len(self)
        return next(reversed(self._commits))

    def _revert(self):
        _, length = self._commits.popitem()
        del self[length:]

    def revert(self, name=None):
        assert len(self._commits) > 0, 'Top of scope. Nothing to revert'
        if name is None or name == next(reversed(self._commits)):
            self._revert()
        else:
            assert name in self._commits
            self._revert()
            self.revert(name)


class Dict(pydantic.generics.GenericModel, typing.Generic[KeyT, DataT]):
    __root__: typing.Mapping[KeyT, DataT]

    _parent = pydantic.PrivateAttr()

    @property
    def parent(self):
        return self._parent

    class Config:
        validate_assignment = True
        extra = 'forbid'
        copy_on_model_validation = False
        allow_mutation = False

    def __init__(self, *args, **kwargs):
        if '__root__' not in kwargs:
            if len(args) == 1:
                kwargs['__root__'] = args[0]
                args = tuple()
            elif len(args) == 0:
                kwargs['__root__'] = {}
        self._parent = _ctx.get()
        with set_context(self):
            super().__init__(*args, **kwargs)

    def items(self):
        return self.__root__.items()

    def keys(self):
        return self.__root__.keys()

    def values(self):
        return self.__root__.values()

    def __len__(self):
        return len(self.__root__)

    def __getitem__(self, item):
        return self.__root__[item]

    def __setitem__(self, item, value):
        self.__root__[item] = value

    def __eq__(self, other):
        return self.__root__ == other

    def __contains__(self, item):
        return item in self.__root__

    def update(self, other):
        self.__root__.update(other)


class SpiceStr(str):

    def __eq__(self, other):
        return isinstance(other, str) and \
            super().casefold() == other.casefold()

    def __add__(self, s: str) -> str:
        return type(self)(super().__add__(s))

    def __hash__(self) -> int:
        return super().casefold().__hash__()

    def __contains__(self, other):
        return isinstance(other, str) and \
            super().casefold().__contains__(other.casefold())

    def startswith(self, prefix) -> bool:
        return isinstance(prefix, str) and \
            super().casefold().startswith(prefix.casefold())

    def endswith(self, suffix) -> bool:
        return isinstance(suffix, str) and \
            super().casefold().endswith(suffix.casefold())

    @classmethod
    def __get_validators__(cls):
        # declare validator to call
        yield cls.validate

    @classmethod
    def validate(cls, v):
        # force casting to 'SpiceStr' instead of 'str'
        return cls(v)
