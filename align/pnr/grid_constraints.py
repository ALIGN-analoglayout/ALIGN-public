import math
from itertools import product
from functools import reduce

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
