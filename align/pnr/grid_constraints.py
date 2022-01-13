import math
from itertools import product
from functools import reduce
from collections import defaultdict
from .hpwl import compute_topoorder
import logging

from ..schema.constraint import OffsetsScalings, PlaceOnGrid

logger = logging.getLogger(__name__)

def check(r, x, scaling):
    return any((x % r.pitch) in ored_term.offsets and
               scaling in ored_term.scalings
               for ored_term in r.ored_terms)

def simplify(pairs):
    offsets_with_pos_scaling = {o for o, s in pairs if s == 1}
    offsets_with_neg_scaling = {o for o, s in pairs if s == -1}
    offsets_with_both_scalings = offsets_with_pos_scaling.intersection(offsets_with_neg_scaling)
    offsets_with_pos_scaling -= offsets_with_both_scalings
    offsets_with_neg_scaling -= offsets_with_both_scalings
    if offsets_with_both_scalings:
        yield OffsetsScalings(offsets=sorted(offsets_with_both_scalings), scalings=[1, -1])
    if offsets_with_pos_scaling:
        yield OffsetsScalings(offsets=sorted(offsets_with_pos_scaling), scalings=[1])
    if offsets_with_neg_scaling:
        yield OffsetsScalings(offsets=sorted(offsets_with_neg_scaling), scalings=[-1])


def lcm(*xs):
    def lcm2(a, b):
        return (a*b) // math.gcd(a, b)
    assert xs
    if len(xs) == 1:
        return xs[0]
    else:
        return reduce(lcm2, xs)


def merge(*rs):
    new_pitch = lcm(*(r.pitch for r in rs))
    new_direction = rs[0].direction
    assert all(new_direction == r.direction for r in rs)

    def gen_pairs(r):
        for coarse_offset in range(0, new_pitch, r.pitch):
            for ored_term in r.ored_terms:
                for offset, scaling in product(ored_term.offsets, ored_term.scalings):
                    yield (coarse_offset + offset, scaling)

    pairs = set.intersection(*(set(gen_pairs(r)) for r in rs))
    res = PlaceOnGrid(direction=new_direction, pitch=new_pitch, ored_terms=list(simplify(pairs)))

    if not res.ored_terms:
        logger.debug(f'No legal grid positions: {res}')

    return res

def split_directions_and_merge(*rs):
    split_directions = defaultdict(list)
    for r in rs:
        split_directions[r.direction].append(r)

    return [merge(*v) for v in split_directions.values()]


def gen_constraints_for_module(m, modules, leaves):
    pog_constraints = []
    for instance in m['instances']:
        ctn = instance['concrete_template_name']
        constraints = None
        # I don't know why I have to do this: I can't check to see if 'constraints' is in leaves[ctn] (it never is.)
        if ctn in leaves:
            try:
                constraints = leaves[ctn]['constraints']
            except KeyError:
                pass
        elif ctn in modules:
            try:
                constraints = modules[ctn]['constraints']
            except KeyError:
                pass
        else:
            assert False, f'{ctn} not found in leaves or modules.'

        print(constraints)

        place_on_grid_constraints = []
        if constraints is not None:
            new_constraints = [constraint.dict() if type(constraint) != dict else constraint for constraint in constraints]
            place_on_grid_constraints = [constraint for constraint in new_constraints if constraint['constraint'] == 'place_on_grid']

        tr = instance['transformation']

        for pog in place_on_grid_constraints:
            if pog['direction'] == 'H': 
                s, o = tr['sX'], tr['oX']
            elif pog['direction'] == 'V':
                s, o = tr['sY'], tr['oY']
            else:
                assert False, pog['direction']

            new_ored_terms = []
            for ored_term in pog['ored_terms']:
                for offset, scaling in product(ored_term['offsets'], ored_term['scalings']):
                    new_offset = (offset-s*o*scaling) % pog['pitch']
                    new_scaling = s*scaling
                    new_ored_terms.append(OffsetsScalings(offsets=[new_offset],scalings=[new_scaling]))

            pog_constraints.append(PlaceOnGrid(direction=pog['direction'], pitch=pog['pitch'], ored_terms=new_ored_terms))

    if pog_constraints:
        m['constraints'].extend(cnst.dict() for cnst in split_directions_and_merge(*pog_constraints))


def gen_constraints(placement_verilog_d, top_level_name):

    modules = {module['concrete_name']: module for module in placement_verilog_d['modules']}
    leaves = {leaf['concrete_name']: leaf for leaf in placement_verilog_d['leaves']}

    order, _, _ = compute_topoorder(modules, top_level_name)

    for concrete_name in order:
        if concrete_name in modules:
            gen_constraints_for_module(modules[concrete_name], modules, leaves)
        else:
            assert concrete_name in leaves
