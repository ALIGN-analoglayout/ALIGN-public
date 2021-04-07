import pydantic.generics
import typing

class BaseModel(pydantic.BaseModel):

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        copy_on_model_validation = False

KeyT = typing.TypeVar('KeyT')
DataT = typing.TypeVar('DataT')

class List(pydantic.generics.GenericModel, typing.Generic[DataT]):
    __root__: typing.Sequence[DataT]

    class Config:
        validate_assignment = True
        extra = 'forbid'
        copy_on_model_validation = False
        allow_mutation = False
        
    def append(self, data: DataT):
        return self.__root__.append(data)

    def remove(self, data: DataT):
        return self.__root__.remove(data)

    def __len__(self):
        return len(self.__root__)

    def __iter__(self):
        return iter(self.__root__)

    def __getitem__(self, item):
        return self.__root__[item]

    def __delitem__(self, sliceobj):
        del self.__root__[sliceobj]

    def __eq__(self, other):
        return self.__root__ == other

class Dict(pydantic.generics.GenericModel, typing.Generic[KeyT,DataT]):
    __root__: typing.Mapping[KeyT, DataT]

    class Config:
        validate_assignment = True
        extra = 'forbid'
        copy_on_model_validation = False
        allow_mutation = False

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

    def __eq__(self, other):
        return self.__root__ == other

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

__all__ = [
    'BaseModel', 'List', 'Dict',
    'validator', 'root_validator', 'validate_arguments',
    'Optional', 'Union',
    'NamedTuple', 'Literal',
    'ClassVar', 'PrivateAttr'
            ]