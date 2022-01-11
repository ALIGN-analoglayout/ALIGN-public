import math
from itertools import product
from functools import reduce
from collections import defaultdict

from ..schema.constraint import OffsetsScalings, PlaceOnGrid

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
    return PlaceOnGrid(direction=new_direction, pitch=new_pitch, ored_terms=list(simplify(pairs)))

def split_directions_and_merge(*rs):
    split_directions = defaultdict(list)
    for r in rs:
        split_directions[r.direction].append(r)

    return [merge(*v) for v in split_directions.values()]


def gen_constraints(placement_verilog_d):
    """Assumes the leaves include the constraint metadata
"""
    
    # Find the top level or internal hierarchy cells 
    # for now let's do the top

    leaves = {leaf['concrete_name']: leaf for leaf in placement_verilog_d['leaves']}

    assert len(placement_verilog_d['modules']) == 1
    top_module = placement_verilog_d['modules'][0]

    pog_constraints = []
    for instance in top_module['instances']:
        ctn = instance['concrete_template_name']
        leaf = leaves[ctn]
        place_on_grid_cnsts = [cnst for cnst in leaf['constraints'] if cnst['constraint'] == 'place_on_grid']

        tr = instance['transformation']
        assert tr['sX'] == 1 and tr['sY'] == 1

        print(ctn, instance['instance_name'], tr, place_on_grid_cnsts)

        for pog in place_on_grid_cnsts:
            if pog['direction'] == 'H':
                delta = tr['oX']
            elif pog['direction'] == 'V':
                delta = tr['oY']
            else:
                assert False, pog['direction']

            new_ored_terms = []
            for ored_term in pog['ored_terms']:
                new_offsets = []
                for offset in ored_term['offsets']:
                    new_offsets.append(offset-delta)

                new_ored_terms.append(OffsetsScalings(offsets=new_offsets,scalings=ored_term['scalings']))

            pog_constraints.append(PlaceOnGrid(direction=pog['direction'], pitch=pog['pitch'], ored_terms=new_ored_terms))

    res = split_directions_and_merge(*pog_constraints)
    print(res)

    return res
