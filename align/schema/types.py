import typing
import pydantic

from typing import TypeVar, Optional, Generic, Union, NamedTuple, Literal, ClassVar, Sequence, Mapping
from pydantic.generics import GenericModel
from pydantic import PrivateAttr

KeyT = TypeVar('KeyT')
DataT = TypeVar('DataT')

class List(GenericModel, Generic[DataT]):
    __root__: Sequence[DataT]

    class Config:
        copy_on_model_validation = False

    @pydantic.validate_arguments
    def append(self, data: DataT):
        return self.__root__.append(data)

    @pydantic.validate_arguments
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

class Dict(GenericModel, Generic[KeyT,DataT]):
    __root__: Mapping[KeyT, DataT]

    class Config:
        copy_on_model_validation = False

    def items(self):
        return self.__root__.items()

    def keys(self):
        return self.__root__.keys()

    def values(self):
        return self.__root__.values()

    def __len__(self):
        return len(self.__root__)

    def __iter__(self):
        return iter(self.__root__)

    def __getitem__(self, item):
        return self.__root__[item]

    def __eq__(self, other):
        return self.__root__ == other
