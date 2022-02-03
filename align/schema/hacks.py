'''
These hacked data structures emulate dictionaries used in
   our existing flow but allow us to insert, validate &
   use formal constraints in ConstraintDB. They serve to
   boostrap our transition from ALIGN 1.0 to 2.0

TODO: Eliminate this module by replacing these data
      structures with SubCircuit, Instance etc.
'''

import itertools

from typing import Any
from .types import BaseModel, List, Dict, set_context, Optional
from .constraint import ConstraintDB

from . import checker
from . import types

import logging
logger = logging.getLogger(__name__)

class DictEmulator(BaseModel):

    class Config:
        extra = 'allow'
        allow_mutation = True

    def __getitem__(self, item):
        return getattr(self, item)

    def __setitem__(self, item, value):
        setattr(self, item, value)

    def __delitem__(self, item):
        delattr(self, item)

    def __contains__(self, item):
        return hasattr(self, item)


class FormalActualMap(DictEmulator):
    formal: str
    actual: str


class VerilogJsonInstance(DictEmulator):
    instance_name: str
    fa_map: List[FormalActualMap]

    def translate(self, solver):
        '''
        Bounding boxes must have non-zero
        height & width
        '''
        b = solver.bbox_vars(self.instance_name)
        yield b.llx < b.urx
        yield b.lly < b.ury


class VerilogJsonModule(DictEmulator):
    #name: str
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

    def translate(self, solver):
        # Initialize subcircuit bounding box
        bb = solver.bbox_vars('subcircuit')
        yield bb.llx < bb.urx
        yield bb.lly < bb.ury
        # Initialize element bounding boxes
        yield from self.instances.translate(solver)
        bvars = solver.iter_bbox_vars([x.instance_name for x in self.instances])
        # Elements must be within subckt bbox
        for b in bvars:
            yield b.llx >= bb.llx
            yield b.lly >= bb.lly
            yield b.urx <= bb.urx
            yield b.ury <= bb.ury
        # Elements may not overlap with each other
        for b1, b2 in itertools.combinations(bvars, 2):
            yield solver.Or(
                b1.urx <= b2.llx,
                b2.urx <= b1.llx,
                b1.ury <= b2.lly,
                b2.ury <= b1.lly,
            )
        # Load constraints
        yield from self.constraints.translate(solver)

    def verify(self, constraint=None):
        if constraint is None:
            self._checker = checker.Z3Checker()
            formulae = self.translate(self._checker)
        else:
            assert self._checker is not None, "Incremental verification is not possible as solver hasn't been instantiated yet"
            formulae = types.cast_to_solver(constraint, self._checker)
        for x in formulae:
            self._checker.append(x)
        try:
            self._checker.solve()
        except checker.SolutionNotFoundError as e:
            logger.debug(f'Checker raised error:\n {e}')
            core = [x.json() for x in itertools.chain(self.instances, self.constraints, [constraint]) if self._checker.label(x) in e.labels]
            logger.error(f'Solution not found due to conflict between:')
            for x in core:
                logger.error(f'{x}')
            raise # checker.SolutionNotFoundError(message=e.message, labels=e.labels)

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr(None)


class VerilogJsonTop(DictEmulator):
    modules: List[VerilogJsonModule]
    leaves: Optional[List[Dict]]
