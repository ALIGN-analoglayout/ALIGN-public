'''
These hacked data structures emulate dictionaries used in
   our existing flow but allow us to insert, validate &
   use formal constraints in ConstraintDB. They serve to
   boostrap our transition from ALIGN 1.0 to 2.0

TODO: Eliminate this module by replacing these data
      structures with SubCircuit, Instance etc.
'''

from typing import Any
from .types import BaseModel, List, Dict, set_context, Optional
from .constraint import ConstraintDB


class DictEmulator(BaseModel):

    class Config:
        extra = 'allow'
        allow_mutation = True

    def __getitem__(self, item):
        return getattr(self, item)

    def __setitem__(self, item, value):
        setattr(self, item, value)

    def __contains__(self, item):
        return hasattr(self, item)


class HierDictNode(DictEmulator):
    name: str
    graph: Any
    ports: List
    constraints: ConstraintDB
    ports_weight: Dict

    def __init__(self, *args, **kwargs):
        constraints = []
        if 'constraints' in kwargs:
            constraints = kwargs['constraints']
        kwargs['constraints'] = []
        super().__init__(*args, **kwargs)
        with set_context(self.constraints):
            self.constraints.extend(constraints)


class FormalActualMap(DictEmulator):
    formal: str
    actual: str


class VerilogJsonInstance(DictEmulator):
    template_name: str
    instance_name: str
    fa_map: List[FormalActualMap]


class VerilogJsonModule(DictEmulator):
    name: str
    parameters: List[str]
    constraints: ConstraintDB
    instances: List[VerilogJsonInstance]

    def __init__(self, *args, **kwargs):
        constraints = []
        if 'constraints' in kwargs:
            constraints = kwargs['constraints']
        kwargs['constraints'] = []
        super().__init__(*args, **kwargs)
        with set_context(self.constraints):
            self.constraints.extend(constraints)


class VerilogJsonTop(DictEmulator):
    modules: List[VerilogJsonModule]
    leaves: Optional[List[Dict]]