import itertools
import logging
from .types import Optional, List, Dict

from . import types
from pydantic import validator

from .types import set_context
from .model import Model
from .instance import Instance
from .constraint import ConstraintDB
from . import checker

import logging
logger = logging.getLogger(__name__)


class SubCircuit(Model):
    name: str                 # Model Name
    pins: Optional[List[str]]  # List of pin names (derived from base if base exists)
    parameters: Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    elements: List[Instance]
    constraints: ConstraintDB
    prefix: str = 'X'         # Instance name prefix, optional

    @property
    def nets(self):
        nets = []
        for element in self.elements:
            nets.extend(x for x in element.pins.values() if x not in nets)
        return nets

    def get_element(self, name):
        return next((x for x in self.elements if x.name == name.upper()), None)

    def update_element(self, name, kwargs):
        i, inst = next(((i, x) for i, x in enumerate(self.elements) if x.name == name.upper()), None)
        with set_context(self.elements):
            new_inst = Instance(name=name,
                                model=(kwargs['model'] if 'model' in kwargs else inst.model),
                                pins=(kwargs['pins'] if 'pins' in kwargs else inst.pins),
                                parameters=(kwargs['parameters'] if 'parameters' in kwargs else inst.parameters),
                                generator=(kwargs['generator'] if 'generator' in kwargs else inst.generator)
                                )
            self.elements[i] = new_inst

    def __init__(self, *args, **kwargs):
        # make elements optional in __init__
        # TODO: Replace with default factory
        if 'elements' not in kwargs:
            kwargs['elements'] = []
        # defer constraint processing for now
        constraints = []
        if 'constraints' in kwargs:
            constraints = kwargs['constraints']
        kwargs['constraints'] = []
        # load subcircuit
        super().__init__(*args, **kwargs)
        # process constraints
        with types.set_context(self.constraints):
            self.constraints.extend(constraints)
    # TODO: Add validator for duplicate name
    # TODO: Add validator for duplicate pins

    def xyce(self):
        ret = []
        for constraint in self.constraints:
            ret.append(f'* @: {constraint}')
        ret.append(f'.SUBCKT {self.name} ' + ' '.join(f'{x}' for x in self.pins))
        ret.extend([f'.PARAM {x}=' + (f'{{{y}}}' if isinstance(y, str) else f'{y}') for x, y in self.parameters.items()])
        ret.extend([element.xyce() for element in self.elements])
        ret.append(f'.ENDS {self.name}')
        return '\n'.join(ret)

    def translate(self, solver):
        # Initialize subcircuit bounding box
        bb = solver.bbox_vars('subcircuit')
        yield bb.llx < bb.urx
        yield bb.lly < bb.ury
        # Initialize element bounding boxes
        yield from self.elements.translate(solver)
        bvars = solver.iter_bbox_vars([x.name for x in self.elements])
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

    def verify(self, formulae=None):
        if formulae is None:
            self._checker = checker.Z3Checker()
            formulae = self.translate(self._checker)
        else:
            assert self._checker is not None, "Incremental verification is not possible as solver hasn't been instantiated yet"
        for x in formulae:
            self._checker.append(x)
        self._check()

    #
    # Private attribute affecting class behavior
    #
    _checker = types.PrivateAttr(None)

    def _check(self):
        try:
            self._checker.solve()
        except checker.SolutionNotFoundError as e:
            logger.debug(f'Checker raised error:\n {e}')
            core = [x.json() for x in itertools.chain(self.elements, self.constraints) if self._checker.label(x) in e.labels]
            logger.error(f'Solution not found due to conflict between:')
            for x in core:
                logger.error(f'{x}')
            raise checker.SolutionNotFoundError(message=e.message, labels=e.labels)


class Circuit(SubCircuit):

    name: Optional[str]
    pins: Optional[List[str]]

    def xyce(self):
        return '\n'.join([element.xyce() for element in self.elements])

    @types.validator('pins')
    def pin_check(cls, pins, values):
        if pins:
            pins = [p.upper() for p in pins]
        return pins

    @types.validator('name', allow_reuse=True)
    def name_is_unique(cls, name, values):
        assert isinstance(cls._validator_ctx().parent, List[Instance]), 'subckt can only be instanitated within List[Instance]'
        assert cls._validator_ctx().parent is not None, 'subckt can only be instantiated within a library'
        assert cls._validator_ctx().parent.find(name) is None, f'Existing subckt definition found {name}'
        return name
