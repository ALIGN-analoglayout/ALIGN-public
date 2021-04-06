import abc
import random
import string
import collections
import more_itertools as itertools

from . import types
from .types import Union, Optional, Literal, List

import logging
logger = logging.getLogger(__name__)

try:
    import z3
except:
    z3 = None
    logger.warning("Could not import z3. ConstraintDB will not look for spec inconsistency.")


class ConstraintBase(types.BaseModel, abc.ABC):

    @abc.abstractmethod
    def check(self):
        '''
        Abstract Method for built in self-checks
          Every class that inherits from ConstraintBase
          MUST implement this function. Please check minimum
          number of arguments at the very least

        :return list of z3 constraints
        '''
        assert len(self.instances) >= 1
        constraints = []
        bvars = self._get_bbox_vars(self.instances)
        for b in bvars:
            constraints.append(b.llx < b.urx)
            constraints.append(b.lly < b.ury)
        return constraints

    @staticmethod
    def _get_bbox_vars(*instances):
        '''
        This function can be used in two ways:
        1) Get all bboxes for a list set of instances:
           (Useful for constraints that accept lists)
            l_bbox = self._z3_bbox_variables(instances)
        2) Choose which instances to get bbox vars for:
           (Useful for pairwise constraints)
            bbox1, bbox2 = self._z3_bbox_variables(box1, box2)
        '''
        print([block for block in instances])
        if len(instances) == 1 and isinstance(instances[0], List):
            instances = instances[0]
        return [ConstraintDB.GenerateVar(
                    'Bbox',
                    llx = f'{block}_llx',
                    lly = f'{block}_lly',
                    urx = f'{block}_urx',
                    ury = f'{block}_ury') \
                for block in instances]

    @staticmethod
    def abs(x):
        return z3.If(x >= 0, x, -x)
    
    @staticmethod
    def min(x, y):
        return z3.If(x<=y, x, y)
    
    @staticmethod
    def max(x, y):
        return z3.If(x>=y, x, y)
