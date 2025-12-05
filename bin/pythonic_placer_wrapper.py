#!/usr/bin/env python
import json
import plotly.graph_objects as go
import plotly.express as px

import mip
import time
import copy
import itertools
import more_itertools
import networkx as nx
from collections import defaultdict
import numpy
import random
import z3

import align.schema.constraint as constraint_schema
from align.schema.hacks import VerilogJsonTop
from align.pnr.checker import check_placement
from align.pnr.grid_constraints import gen_constraints_for_module
from align.cell_fabric.transformation import Transformation, Rect

class HyperParameters:
    max_sequence_pairs = 10000
    max_block_variants = 100
    max_candidates = 10000
    max_solutions = 4
    Tmax = 0.5
    Tmin = 0.05
    alpha = 0.9995

    LAMBDA=1.0

def measure_time(func):
    def wrapper(*args, **kwargs):
        s = time.time()
        returned_value = func(*args, **kwargs)
        e = time.time() - s
        print(f'Elapsed time: {e:.3f} secs')
        return returned_value
    return wrapper

class sequence_pair_enumerator:
    def __init__(self, N:int, order:defaultdict, symmetry:defaultdict):
        self.pseq = [z3.Int("p_%s" % i) for i in range(N)]
        self.nseq = [z3.Int("n_%s" % i) for i in range(N)]
        self.solver = z3.Solver()
        self.N = N
        pseq, nseq = self.pseq, self.nseq
        self.solver.add([z3.And(0 <= pseq[i], pseq[i] <= (N-1), 0 <= nseq[i], nseq[i] <= (N-1)) for i in range(N)])
    
        self.solver.add(z3.Distinct([pseq[i] for i in range(N)]))
        self.solver.add(z3.Distinct([nseq[i] for i in range(N)]))
    
    # ordering constraint
        for key, val in order.items():
            for blocks in val:
                nblocks = len(blocks) - 1
                if key == 'left_to_right':  # (before, before)
                    self.solver.add(z3.And([pseq[blocks[i]] < pseq[blocks[i + 1]] for i in range(nblocks)]))
                    self.solver.add(z3.And([nseq[blocks[i]] < nseq[blocks[i + 1]] for i in range(nblocks)]))
                elif key == 'right_to_left': # (after, after)
                    self.solver.add(z3.And([pseq[blocks[i]] > pseq[blocks[i + 1]] for i in range(nblocks)]))
                    self.solver.add(z3.And([nseq[blocks[i]] > nseq[blocks[i + 1]] for i in range(nblocks)]))
                elif key == 'bottom_to_top': # (after, before)
                    self.solver.add(z3.And([pseq[blocks[i]] > pseq[blocks[i + 1]] for i in range(nblocks)]))
                    self.solver.add(z3.And([nseq[blocks[i]] < nseq[blocks[i + 1]] for i in range(nblocks)]))
                elif key == 'top_to_bottom': # (before, after)
                    self.solver.add(z3.And([pseq[blocks[i]] < pseq[blocks[i + 1]] for i in range(nblocks)]))
                    self.solver.add(z3.And([nseq[blocks[i]] > nseq[blocks[i + 1]] for i in range(nblocks)]))
    # symmetry constraint: 'V': pairs should be left or right and pairs should be both above or below self_sym
    # symmetry constraint: 'H': pairs should be above or below and pairs should be both left or right self_sym
        for key, val in symmetry.items():
            for blocks in val:
                units = [blocks[i][0] for i in range(len(blocks)) if len(blocks[i]) == 1]
                pairs = [blocks[i] for i in range(len(blocks)) if len(blocks[i]) == 2]
                for u in units:
                    for p in pairs:
                        if key == 'V':
                            # self_sym either above or below the pair or sandwiched
                            self.solver.add(
                                    z3.Or(
                                        z3.And(pseq[u] > pseq[p[0]], pseq[u] > pseq[p[1]], nseq[u] < nseq[p[0]], nseq[u] < nseq[p[1]]),
                                        z3.And(pseq[u] < pseq[p[0]], pseq[u] < pseq[p[1]], nseq[u] > nseq[p[0]], nseq[u] > nseq[p[1]]),
                                        z3.And(pseq[u] > pseq[p[0]], pseq[u] < pseq[p[1]], nseq[u] > nseq[p[0]], nseq[u] < nseq[p[1]]),
                                        z3.And(pseq[u] < pseq[p[0]], pseq[u] > pseq[p[1]], nseq[u] < nseq[p[0]], nseq[u] > nseq[p[1]])
                                        )
                                    )
                        elif key == 'H':
                            # self_sym either left or right of the pair or sandwiched
                            self.solver.add(
                                    z3.Or(
                                        z3.And(pseq[u] > pseq[p[0]], pseq[u] > pseq[p[1]], nseq[u] > nseq[p[0]], nseq[u] > nseq[p[1]]),
                                        z3.And(pseq[u] < pseq[p[0]], pseq[u] < pseq[p[1]], nseq[u] < nseq[p[0]], nseq[u] < nseq[p[1]]),
                                        z3.And(pseq[u] > pseq[p[0]], pseq[u] < pseq[p[1]], nseq[u] < nseq[p[0]], nseq[u] > nseq[p[1]]),
                                        z3.And(pseq[u] < pseq[p[0]], pseq[u] > pseq[p[1]], nseq[u] > nseq[p[0]], nseq[u] < nseq[p[1]])
                                        )
                                    )
    
                if len(units):
                    for i in range(len(units)):
                        for j in range(i + 1, len(units)):
                            if key == 'V':
                                # units are vertical
                                self.solver.add(
                                        z3.Or(
                                            z3.And(pseq[units[i]] > pseq[units[j]], nseq[units[i]] < nseq[units[j]]),
                                            z3.And(pseq[units[i]] < pseq[units[j]], nseq[units[i]] > nseq[units[j]])
                                            )
                                        )
                            elif key == 'H':
                                # units are horizontal
                                self.solver.add(
                                        z3.Or(
                                            z3.And(units[i][units[i]] > pseq[units[j]], nseq[units[i]] > nseq[units[j]]),
                                            z3.And(units[i][units[i]] < pseq[units[j]], nseq[units[i]] < nseq[units[j]])
                                            )
                                        )
    
                for p in pairs:
                    if key == 'V':
                        # pair is horizontal
                        self.solver.add(
                                z3.Or(
                                    z3.And([pseq[p[0]] > pseq[p[1]], nseq[p[0]] > nseq[p[1]]]),
                                    z3.And([pseq[p[0]] < pseq[p[1]], nseq[p[0]] < nseq[p[1]]])
                                    )
                                )
                    elif key == 'H':
                        # pair is vertical
                        self.solver.add(
                                z3.Or(
                                    z3.And([pseq[p[0]] > pseq[p[1]], nseq[p[0]] < nseq[p[1]]]),
                                    z3.And([pseq[p[0]] < pseq[p[1]], nseq[p[0]] > nseq[p[1]]])
                                    )
                                )
                for i in range(len(pairs)):
                    p = pairs[i]
                    for j in range(i + 1, len(pairs)):
                        q = pairs[j]
                        if key == 'V':
                            # pairs or above/below or sandwiched
                            self.solver.add(
                                    z3.Or(
                                        z3.And(
                                            pseq[p[0]] > pseq[q[0]], pseq[p[1]] > pseq[q[0]], nseq[p[0]] < nseq[q[0]], nseq[p[1]] < nseq[q[0]],
                                            pseq[p[0]] > pseq[q[1]], pseq[p[1]] > pseq[q[0]], nseq[p[0]] < nseq[q[1]], nseq[p[1]] < nseq[q[1]]
                                            ), # above/below
                                        z3.And(
                                            pseq[p[0]] < pseq[q[0]], pseq[p[1]] < pseq[q[0]], nseq[p[0]] > nseq[q[0]], nseq[p[1]] > nseq[q[0]],
                                            pseq[p[0]] < pseq[q[1]], pseq[p[1]] < pseq[q[1]], nseq[p[0]] > nseq[q[1]], nseq[p[1]] > nseq[q[1]]
                                            ),
                                        z3.And(pseq[p[0]] < pseq[q[0]], pseq[p[1]] > pseq[q[1]], nseq[p[0]] < nseq[q[0]], nseq[p[1]] > nseq[q[1]]), # sandwiched
                                        z3.And(pseq[p[0]] < pseq[q[1]], pseq[p[1]] > pseq[q[0]], nseq[p[1]] < nseq[q[0]], nseq[p[1]] > nseq[q[0]]), 
                                        z3.And(pseq[p[0]] > pseq[q[0]], pseq[p[1]] < pseq[q[1]], nseq[p[0]] > nseq[q[0]], nseq[p[1]] < nseq[q[1]]),
                                        z3.And(pseq[p[0]] > pseq[q[1]], pseq[p[1]] < pseq[q[0]], nseq[p[0]] > nseq[q[1]], nseq[p[1]] < nseq[q[0]])
                                        )
                                    )
                        elif key == 'H':
                            # self_sym either left or right of the pair or sandwiched
                            self.solver.add(
                                    z3.Or(
                                        z3.And(
                                            pseq[p[0]] > pseq[q[0]], pseq[p[1]] > pseq[q[0]], nseq[p[0]] > nseq[q[0]], nseq[p[1]] > nseq[q[0]],
                                            pseq[p[0]] > pseq[q[1]], pseq[p[1]] > pseq[q[1]], nseq[p[0]] > nseq[q[1]], nseq[p[1]] > nseq[q[1]]
                                            ), # left/right
                                        z3.And(
                                            pseq[p[0]] < pseq[q[0]], pseq[p[1]] < pseq[q[0]], nseq[p[0]] < nseq[q[0]], nseq[p[1]] < nseq[q[0]],
                                            pseq[p[0]] < pseq[q[1]], pseq[p[1]] < pseq[q[1]], nseq[p[0]] < nseq[q[1]], nseq[p[1]] < nseq[q[1]]
                                            ),
                                        z3.And(pseq[p[0]] < pseq[q[0]], pseq[p[1]] > pseq[q[1]], nseq[p[0]] > nseq[q[0]], nseq[p[1]] < nseq[q[1]]), # sandwiched
                                        z3.And(pseq[p[0]] < pseq[q[1]], pseq[p[1]] > pseq[q[0]], nseq[p[1]] > nseq[q[0]], nseq[p[1]] < nseq[q[0]]), 
                                        z3.And(pseq[p[0]] > pseq[q[0]], pseq[p[1]] < pseq[q[1]], nseq[p[0]] < nseq[q[0]], nseq[p[1]] > nseq[q[1]]),
                                        z3.And(pseq[p[0]] > pseq[q[1]], pseq[p[1]] < pseq[q[0]], nseq[p[0]] < nseq[q[1]], nseq[p[1]] > nseq[q[0]])
                                        )
                                    )
    
    def get_seq(self):
        if self.solver.check() == z3.sat:
            pos_seq = [0] * self.N
            neg_seq = [0] * self.N
            model = self.solver.model()
            for i in range(self.N):
                pos_seq[model[self.pseq[i]].as_long()] = i
                neg_seq[model[self.nseq[i]].as_long()] = i
            sol = z3.And([v == z3.IntVal(model[v]) for v in (self.pseq + self.nseq) ])
            self.solver.append(z3.Not(sol))
            return (pos_seq, neg_seq)
        return None


def enumerate_sequence_pairs(constraints, instance_map: dict, max_sequences: int):

    """
    # Initialize constraint graphs
    pos_graph = nx.DiGraph()
    neg_graph = nx.DiGraph()
    pos_graph.add_nodes_from(range(len(instance_map)))
    neg_graph.add_nodes_from(range(len(instance_map)))

    # Add edges to constraint graphs
    for constraint in constraint_schema.expand_user_constraints(constraints):
        if isinstance(constraint, constraint_schema.Order):
            for i0, i1 in more_itertools.pairwise(constraint.instances):
                if constraint.direction == 'left_to_right':    # (before,before)
                    pos_graph.add_edge(instance_map[i0], instance_map[i1])
                    neg_graph.add_edge(instance_map[i0], instance_map[i1])

                elif constraint.direction == 'right_to_left':  # (after, after)
                    pos_graph.add_edge(instance_map[i1], instance_map[i0])
                    neg_graph.add_edge(instance_map[i1], instance_map[i0])

                elif constraint.direction == 'bottom_to_top':  # (after, before)
                    pos_graph.add_edge(instance_map[i1], instance_map[i0])
                    neg_graph.add_edge(instance_map[i0], instance_map[i1])

                elif constraint.direction == 'top_to_bottom':  # (before, after)
                    pos_graph.add_edge(instance_map[i0], instance_map[i1])
                    neg_graph.add_edge(instance_map[i1], instance_map[i0])
                else:
                    pass

    # Generate sequences using topological sort
    count = 1
    sequence_pairs = list()
    for pos in nx.all_topological_sorts(pos_graph):
        for neg in nx.all_topological_sorts(neg_graph):
            sequence_pairs.append((tuple(pos), tuple(neg)))
            count += 1
            if count > 10*max_sequences:
                break
        if count > 10*max_sequences:
            break
    """
    order = defaultdict(list)
    symm  = defaultdict(list)
    for constraint in constraint_schema.expand_user_constraints(constraints):
        if isinstance(constraint, constraint_schema.Order):
            order[constraint.direction].append([instance_map[i] for i in constraint.instances])
        elif isinstance(constraint, constraint_schema.SymmetricBlocks):
            pairs = getattr(constraint, 'pairs')
            symm[getattr(constraint, 'direction')].append([[instance_map[i] for i in pair] for pair in pairs])
    sp_enum = sequence_pair_enumerator(len(instance_map), order, symm)
    sequence_pairs = list()
    count = 1
    ps = sp_enum.get_seq()
    while (count <= max_sequences) and ps:
        sequence_pairs.append(ps)
        ps = sp_enum.get_seq()
        count += 1

    return sequence_pairs


def enumerate_block_variants(constraints, instance_map: dict, variant_counts: dict, max_variants: int):

    # Group instances that should use the same concrete template
    groups = list()
    grouped_instances = set()
    for constraint in constraint_schema.expand_user_constraints(constraints):
        if isinstance(constraint, constraint_schema.SameTemplate):
            set_of_instances = set(constraint.instances)
            grouped_instances = set.union(grouped_instances, set_of_instances)
            group_exists = False
            for i, group in enumerate(groups):
                if set.intersection(set_of_instances, group):
                    groups[i] = set.union(set_of_instances, group)
                    group_exists = True
                    break
            if not group_exists:
                groups.append(set_of_instances)

    # Create groups for isolated instances
    for instance in instance_map.keys():
        if instance not in grouped_instances:
            groups.append({instance})

    # Enumerate
    group_variants = list()
    for i, group in enumerate(groups):
        for instance in group:  # get an instance from the set
            break
        group_variants.append([k for k in range(variant_counts[instance])])

    count = 1
    variants = list()
    for variant in itertools.product(*group_variants):
        selection = [0]*len(instance_map)
        for i, v in enumerate(variant):
            # Assign variant v to all instances of i^th group
            for instance in groups[i]:
                selection[instance_map[instance]] = v
        variants.append(tuple(selection))
        if count > max_variants:
            break
    return variants


def place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=None, scale_factor=1):

    model = mip.Model(sense=mip.MINIMIZE, solver_name=mip.CBC)
    model.verbose = 0 # set to one to see more progress output with the solver

    upper_bound = 1e9  # 100mm=100e6nm=1e9 angstrom
    model.add_var(name='W', lb=0, ub=upper_bound)
    model.add_var(name='H', lb=0, ub=upper_bound)

    for name, _ in instance_map.items():

        size = dict(zip('xy', instance_sizes[name]))

        # Define instance variables
        for tag in ['llx', 'lly', 'urx', 'ury']:
            model.add_var(name=f'{name}_{tag}', lb=0, ub=upper_bound)
        for tag in ['fx', 'fy']:
            model.add_var(name=f'{name}_{tag}', var_type=mip.BINARY)

        # Instance width and height
        model += model.var_by_name(f'{name}_urx') - model.var_by_name(f'{name}_llx') == size['x'], f'size_x_{name}'
        model += model.var_by_name(f'{name}_ury') - model.var_by_name(f'{name}_lly') == size['y'], f'size_y_{name}'

        # All instances within the bounding box
        model += model.var_by_name(f'{name}_urx') <= model.var_by_name('W'), f'{name}_W'
        model += model.var_by_name(f'{name}_ury') <= model.var_by_name('H'), f'{name}_H'

    # Constraints implied by the sequence pairs
    reverse_map = {v: k for k, v in instance_map.items()}
    instance_pos = {reverse_map[index]: i for i, index in enumerate(sequence_pair[0])}
    instance_neg = {reverse_map[index]: i for i, index in enumerate(sequence_pair[1])}
    for index0, index1 in itertools.combinations(reverse_map, 2):
        name0 = reverse_map[index0]
        name1 = reverse_map[index1]
        assert name0 != name1
        if instance_pos[name0] < instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:    # bb = LEFT
            model += model.var_by_name(f'{name0}_urx') <= model.var_by_name(f'{name1}_llx'), f'bb_{name0}_{name1}'
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # aa = RIGHT
            model += model.var_by_name(f'{name1}_urx') <= model.var_by_name(f'{name0}_llx'), f'aa_{name0}_{name1}'
        elif instance_pos[name0] < instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # ba = ABOVE
            model += model.var_by_name(f'{name1}_ury') <= model.var_by_name(f'{name0}_lly'), f'ba_{name0}_{name1}'
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:  # ab = BELOW
            model += model.var_by_name(f'{name0}_ury') <= model.var_by_name(f'{name1}_lly'), f'ab_{name0}_{name1}'
        else:
            assert False

    # Parse constraints
    net_priority = dict()
    ctr = 0
    for constraint in constraint_schema.expand_user_constraints(constraints):

        if isinstance(constraint, constraint_schema.Boundary):
            if max_width := getattr(constraint, 'max_width', False):
                model += model.var_by_name('W') <= max_width, f'boundary_W'
            if max_height := getattr(constraint, 'max_height', False):
                model += model.var_by_name('H') <= max_height, f'boundary_H'

        elif isinstance(constraint, constraint_schema.PlaceOnBoundary):
            for name in constraint.instances_on(['north', 'northwest', 'northeast']):
                model += model.var_by_name(f'{name}_ury') == model.var_by_name('H'), f'boundary_ury_{name}'
            for name in constraint.instances_on(['south', 'southwest', 'southeast']):
                model += model.var_by_name(f'{name}_lly') == 0, f'boundary_lly_{name}'
            for name in constraint.instances_on(['east', 'northeast', 'southeast']):
                model += model.var_by_name(f'{name}_urx') == model.var_by_name('W'), f'boundary_urx_{name}'
            for name in constraint.instances_on(['west', 'northwest', 'southwest']):
                model += model.var_by_name(f'{name}_llx') == 0, f'boundary_llx_{name}'

        elif isinstance(constraint, constraint_schema.NetPriority):
            nets = getattr(constraint, 'nets')
            weight = getattr(constraint, 'weight')
            for net in nets:
                net_priority[net] = weight

        elif isinstance(constraint, constraint_schema.Align):
            instances = getattr(constraint, 'instances')
            line = getattr(constraint, 'line')
            supported_lines = {'h_bottom': 'lly', 'h_top': 'ury', 'v_left': 'llx', 'v_right': 'urx'}
            assert line in supported_lines, f'{line} not supported. Please choose among {supported_lines.keys()}'
            axis = supported_lines[line]
            i0 = instances[0]
            for i1 in instances[1:]:
                model += model.var_by_name(f'{i0}_{axis}') == model.var_by_name(f'{i1}_{axis}'), f'{i0}_{i1}_{axis}'

        elif isinstance(constraint, constraint_schema.SymmetricBlocks):
            pairs = getattr(constraint, 'pairs')
            axis = 'x' if getattr(constraint, 'direction') == 'V' else 'y'
            orth = 'y' if getattr(constraint, 'direction') == 'V' else 'x'
            symmetry_line = model.add_var(lb=0, ub=upper_bound)
            for pair in pairs:
                if len(pair) == 1:
                     #rel_tol = 10  # max distance from symmetry line should be less than 1/10th the block width
                     #model += (1-1/rel_tol)*(model.var_by_name(f'{pair[0]}_ll{axis}') + model.var_by_name(f'{pair[0]}_ur{axis}')) <= 2*symmetry_line
                     #model += (1+1/rel_tol)*(model.var_by_name(f'{pair[0]}_ll{axis}') + model.var_by_name(f'{pair[0]}_ur{axis}')) >= 2*symmetry_line
                    model += (model.var_by_name(f'{pair[0]}_ll{axis}') + model.var_by_name(f'{pair[0]}_ur{axis}')) == 2*symmetry_line, f'symm_{pair[0]}_{ctr}'
                else:
                    model += model.var_by_name(f'{pair[0]}_ll{axis}') + model.var_by_name(f'{pair[0]}_ur{axis}') + \
                             model.var_by_name(f'{pair[1]}_ll{axis}') + model.var_by_name(f'{pair[1]}_ur{axis}') == \
                             4*symmetry_line, f'symm_{pair[0]}_{pair[1]}_{ctr}'
                    model += model.var_by_name(f'{pair[0]}_ll{orth}') == model.var_by_name(f'{pair[1]}_ll{orth}'), f'symm_1_{pair[0]}_{pair[1]}_{ctr}'
            ctr += 1

        elif isinstance(constraint, constraint_schema.Spread):
            instances = getattr(constraint, 'instances')
            distance = getattr(constraint, 'distance') * scale_factor
            axis = 'x' if getattr(constraint, 'direction') == 'horizontal' else 'y'
            # TODO: If the elements are already ordered in sequence pair, no need to introduce a binary variable!
            for i0, i1 in itertools.combinations(instances, 2):
                var = model.add_var(var_type=mip.BINARY)
                model += distance - model.var_by_name(f'{i1}_ll{axis}') + model.var_by_name(f'{i0}_ur{axis}') - upper_bound*var <= 0, f'spread_{i0}_{i1}_{axis}0'
                model += distance - model.var_by_name(f'{i0}_ll{axis}') + model.var_by_name(f'{i1}_ur{axis}') - upper_bound*(1-var) <= 0, f'spread_{i0}_{i1}_{axis}1'

    # Half perimeter wire length
    model.add_var(name='HPWL', lb=0, ub=upper_bound)
    if wires:
        for wire_name, instance_bbox in wires.items():
            for tag, axis in itertools.product(['ll', 'ur'], ['x', 'y']):
                model.add_var(name=f'{wire_name}_{tag}{axis}')

            for instance, bbox in instance_bbox:
                size = dict(zip("xy", instance_sizes[instance]))
                for (tag, axis), offset in zip(itertools.product(['ll', 'ur'], ['x', 'y']), bbox):
                    eqn = model.var_by_name(f'{instance}_ll{axis}') + offset + (size[axis] - 2*offset) * model.var_by_name(f'{instance}_f{axis}')
                    model += eqn <= model.var_by_name(f'{wire_name}_ur{axis}'), f'wl_{wire_name}_ur{axis}_{instance}_{offset}'
                    model += model.var_by_name(f'{wire_name}_ll{axis}') <= eqn, f'wl_{wire_name}_ll{axis}_{instance}_{offset}'

        model += \
            mip.xsum(net_priority.get(wire_name, 1) * model.var_by_name(f'{wire_name}_ur{axis}') for wire_name in wires for axis in ['x', 'y']) - \
            mip.xsum(net_priority.get(wire_name, 1) * model.var_by_name(f'{wire_name}_ll{axis}') for wire_name in wires for axis in ['x', 'y']) == \
            model.var_by_name('HPWL'), f'HPWL_{wire_name}'

    else:
        model += model.var_by_name('HPWL') == 0

    # Minimize the perimeter of the bounding box and normalized HPWL
    scale_hpwl = 1/len(wires) if wires else 1

    model.objective += model.var_by_name('W') + model.var_by_name('H') + scale_hpwl * model.var_by_name('HPWL')

    model.write(f'model.lp')

    # Solve
    model.verbose = 0
    status = model.optimize(max_seconds_same_incumbent=60.0, max_seconds=300)
    if status == mip.OptimizationStatus.OPTIMAL:
        print(f'optimal solution found : objective={model.objective_value}')
    elif status == mip.OptimizationStatus.FEASIBLE:
        print(f'solution with objective {model.objective_value} current lower bound: {model.objective_bound}')
    else:
          #print('No solution to ILP')
        return False

    if status == mip.OptimizationStatus.OPTIMAL or status == mip.OptimizationStatus.FEASIBLE:
        if model.verbose:
            print('Solution:')
            for v in model.vars:
                print('\t', v.name, v.x)
            print(f'Number of solutions: {model.num_solutions}')

    # Extract solution
    transformations = dict()
    for name, _ in instance_map.items():
        fx, fy = model.var_by_name(f'{name}_fx').x, model.var_by_name(f'{name}_fy').x
        ox = model.var_by_name(f'{name}_llx').x + fx * instance_sizes[name][0]
        oy = model.var_by_name(f'{name}_lly').x + fy * instance_sizes[name][1]
        sx = 1 if fx == 0 else -1
        sy = 1 if fy == 0 else -1
        transformations[name] = {'oX': round(ox), 'oY': round(oy), 'sX': sx, 'sY': sy}

    w = round(model.var_by_name('W').x)
    h = round(model.var_by_name('H').x)
    hyper_params = HyperParameters()
    solution = {
        'cost': (w*h + model.var_by_name('HPWL').x * hyper_params.LAMBDA),
        'width': w,
        'height': h,
        'area': w*h,
        'hpwl': model.var_by_name('HPWL').x / scale_hpwl,
        'transformations': transformations,
        'model': model
    }
    return solution

def accept(delC, T):
    if delC <= 0: return True
    delC = numpy.exp(delC)
    return random.random() < numpy.exp(-delC/T)

def place_using_sequence_pairs(placement_data, module, top_level):

    ATN = 'abstract_template_name'
    CTN = 'concrete_template_name'

    hyper_params = HyperParameters()

    instances = {i['instance_name']: i for i in module['instances']}

    instance_map = dict()
    abstract_names = set()
    cnt = 0
    for instance in module['instances']:
        instance_map[instance['instance_name']] = cnt
        abstract_names.add(instance[ATN])
        cnt += 1
    assert cnt > 0, f'Module has no instances: {module}'

    reverse_instance_map = [None] * len(instance_map)
    for k, v in instance_map.items():
        reverse_instance_map[v] = k
     #reverse_instance_map = {v: k for k, v in instance_map.items()}

    variant_map = defaultdict(list)
    for leaf in placement_data['leaves'] + placement_data['modules']:
        if leaf['abstract_name'] in abstract_names:
            variant_map[leaf['abstract_name']].append(leaf)

    variant_counts = dict()
    for instance in module['instances']:
        variant_counts[instance['instance_name']] = len(variant_map[instance[ATN]])

    verilog_json = VerilogJsonTop.parse_obj({'modules': [module]})
    constraints = verilog_json['modules'][0]['constraints']

    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, hyper_params.max_sequence_pairs)
    block_variants = enumerate_block_variants(constraints, instance_map, variant_counts, hyper_params.max_block_variants)

    solutions = list()
    def get_instances_wires(block_variant, reverse_instance_map, variant_map, instances, module):
        instance_sizes = dict()
        wires = defaultdict(list)
        for idx, selected in enumerate(block_variant):
            instance_name = reverse_instance_map[idx]
            concrete_template = variant_map[instances[instance_name][ATN]][selected]
            bbox = concrete_template['bbox']
            instance_sizes[instance_name] = [bbox[2] - bbox[0], bbox[3] - bbox[1]]

            for formal_actual in instances[instance_name]['fa_map']:
                formal, actual = formal_actual['formal'], formal_actual['actual']
                if 'global_signals' not in module or actual not in module['global_signals']:
                    wires[actual].append((instance_name, tuple(x for x in concrete_template['pin_bbox'][formal])))
        return instance_sizes, wires

    if True: #len(sequence_pairs) * len(block_variants) <= hyper_params.max_candidates: # enumerative placer
        for block_variant, sequence_pair in itertools.islice(itertools.product(block_variants, sequence_pairs), hyper_params.max_candidates):

            instance_sizes, wires = get_instances_wires(block_variant, reverse_instance_map, variant_map, instances, module)
            solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=wires, scale_factor=placement_data['scale_factor'])

            if solution:
                solution['sequence_pair'] = sequence_pair
                solution['block_variant'] = block_variant
                solutions.append(solution)
    else:
        assert(hyper_params.alpha < 1. and hyper_params.Tmin < hyper_params.Tmax)
        def perturb(sp, bv):
            seq_pair = [list(sp[0]), list(sp[1])]
            block_variant = copy.deepcopy(bv)
            if len(seq_pair) <= 1: return (tuple(seq_pair[0]), tuple(seq_pair[1])), block_variant
            s = random.randint(0, 2)
            if s <= 1:
                i = random.randint(0, len(seq_pair[0]) - 1)
                j = random.randint(0, len(seq_pair[0]) - 1)
                while j == i:
                    j = random.randint(0, len(seq_pair[0]) - 1)
                pi, pj = seq_pair[0][i], seq_pair[0][j]
                seq_pair[0][i], seq_pair[0][j] = seq_pair[0][j], seq_pair[0][i]
                if s == 1:
                    i, j = seq_pair[1].index(pi), seq_pair[1].index(pj)
                    seq_pair[1][i], seq_pair[1][j] = seq_pair[1][j], seq_pair[1][i]
            elif s == 2:
                block_variant = copy.deepcopy(bv)
            return (tuple(seq_pair[0]), tuple(seq_pair[1])), block_variant
        T = hyper_params.Tmax
        solution = False
        sequence_pair = sequence_pairs[0]
        block_variant = [0] * len(sequence_pair[0])
        count = 0
        while count < hyper_params.max_candidates:
            count += 1
            instance_sizes, wires = get_instances_wires(block_variant, reverse_instance_map, variant_map, instances, module)
            solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=wires, scale_factor=placement_data['scale_factor'])
            if solution:
                solution['sequence_pair'] = sequence_pair
                solution['block_variant'] = block_variant
                solutions.append(solution)
                break
            else:
                sequence_pair, block_variant = perturb(sequence_pair, block_variant)
        if solution: print(f'Found sol {sequence_pair}')
        else: print('No sol found')
        C = solution['cost'] if solution else 0
        minC = C

        while T >= hyper_params.Tmin:
            for i in range(10):
                seq_pair_n, block_variant_n = perturb(sequence_pair, block_variant)
                instance_sizes_n, wires_n = get_instances_wires(block_variant_n, reverse_instance_map, variant_map, instances, module)
                solution = place_sequence_pair(constraints, instance_map, instance_sizes_n, seq_pair_n, wires=wires_n, scale_factor=placement_data['scale_factor'])
                if solution:
                    solution['sequence_pair'] = sequence_pair
                    solution['block_variant'] = block_variant
                    solutions.append(solution)
                    Cnew = solution['cost']
                    if accept(Cnew - C, T):
                        C = Cnew
                        sequence_pair, block_variant = seq_pair_n, block_variant_n
                        if minC >= Cnew:
                            minC = Cnew
            T = T * hyper_params.alpha

    assert solutions, f'No placement solution found for {module["name"]}'

    # Annotate best K solutions to placement_data
    solutions.sort(key=lambda x: x['cost'])
    if len(solutions) > hyper_params.max_solutions:
        solutions = solutions[:hyper_params.max_solutions]

    for i in range(len(solutions)):
        solution = solutions[i]
        new_module = copy.deepcopy(module)
        pin_bbox = dict()
        for instance in new_module['instances']:
            instance_name = instance['instance_name']
            instance['transformation'] = solution['transformations'][instance_name]
            variant_index = solution['block_variant'][instance_map[instance_name]]
            concrete_template = variant_map[instance[ATN]][variant_index]
            instance[CTN] = concrete_template['concrete_name']

            # Annotate bounding box of pins to the module
            for formal_actual in instance['fa_map']:
                formal, actual = formal_actual['formal'], formal_actual['actual']
                if 'global_signals' not in module or actual not in module['global_signals']:
                    rect = concrete_template['pin_bbox'][formal]
                    if not rect:
                        continue
                    rect = Transformation(
                        instance['transformation']['oX'],
                        instance['transformation']['oY'],
                        instance['transformation']['sX'],
                        instance['transformation']['sY']
                        ).hitRect(Rect(*rect)).canonical().toList()

                    if actual not in pin_bbox:
                        pin_bbox[actual] = [x for x in rect]
                    else:
                        pin_bbox[actual][0] = min(pin_bbox[actual][0], rect[0])
                        pin_bbox[actual][1] = min(pin_bbox[actual][1], rect[1])
                        pin_bbox[actual][2] = max(pin_bbox[actual][2], rect[2])
                        pin_bbox[actual][3] = max(pin_bbox[actual][3], rect[3])

        new_module['bbox'] = [0, 0, solution['width'], solution['height']]
        new_module['abstract_name'] = new_module['name']
        new_module['concrete_name'] = new_module['name'] + f'_{i}'
        new_module['pin_bbox'] = pin_bbox
        del new_module['name']

        placement_data['modules'].append(new_module)

        modules = {module['concrete_name']: module for module in placement_data['modules']}
        leaves = {leaf['concrete_name']: leaf for leaf in placement_data['leaves']}
        gen_constraints_for_module(new_module, modules, leaves)

def compute_topoorder(modules, concrete_name, key='abstract_template_name'):
    found_modules, found_leaves = set(), set()
    order = list()

    def aux(cn):
        if cn in modules:
            found_modules.add(cn)
            for instance in modules[cn]['instances']:
                ctn = instance[key]
                if ctn not in found_modules and ctn not in found_leaves:
                    aux(ctn)
            order.append(cn)
        else:
            found_leaves.add(cn)
            order.append(cn)
    aux(concrete_name)

    return order, found_modules, found_leaves


def trim_placement_data(placement_data, top_level):

    modules = {module['concrete_name']: module for module in placement_data['modules']}

    top_concrete_names = [module['concrete_name'] for module in placement_data['modules'] if module['abstract_name'] == top_level]
    all_modules_leaves = set()
    for concrete_name in top_concrete_names:
        _, found_modules, found_leaves = compute_topoorder(modules, concrete_name, key='concrete_template_name')
        all_modules_leaves.update(found_modules)
        all_modules_leaves.update(found_leaves)

    new_placement_data = {'leaves': list(), 'modules': list()}
    for key in ['leaves', 'modules']:
        new_placement_data[key] = [x for x in placement_data[key] if x['concrete_name'] in all_modules_leaves]
        for elem in new_placement_data[key]:
            if 'pin_bbox' in elem:
                del elem['pin_bbox']
            if 'global_signals' in elem:
                elem['global_signals'] = list(elem['global_signals'])

    return new_placement_data


def propagate_down_global_signals(modules: dict, module_name: str, global_signals: set):
    GS = 'global_signals'
    if GS in modules[module_name]:
        modules[module_name][GS].update(global_signals)
    else:
        modules[module_name][GS] = set(global_signals)
    for instance in modules[module_name]['instances']:
        sub_module_name = instance['abstract_template_name']
        if sub_module_name in modules:
            signals_to_propagate = set()
            for formal_actual in instance['fa_map']:
                formal = formal_actual['formal']
                actual = formal_actual['actual']
                if actual in global_signals and formal not in modules[sub_module_name].get(GS, set()):
                    signals_to_propagate.add(formal)
            if signals_to_propagate:
                propagate_down_global_signals(modules, sub_module_name, signals_to_propagate)


def pythonic_placer(top_level, input_data, scale_factor=1):

    placement_data = dict()
    placement_data['modules'] = list()
    placement_data['leaves'] = list()
    placement_data['scale_factor'] = scale_factor
    for leaf in input_data['leaves']:
        # Calculate a bounding box for each pin for HPWL calculation
        pin_bbox = dict()
        for term in leaf['terminals']:
            if term['netType'] == 'pin':
                net_name = term['netName']
                if net_name not in pin_bbox:
                    pin_bbox[net_name] = [x for x in term['rect']]
                else:
                    pin_bbox[net_name][0] = min(pin_bbox[net_name][0], term['rect'][0])
                    pin_bbox[net_name][1] = min(pin_bbox[net_name][1], term['rect'][1])
                    pin_bbox[net_name][2] = max(pin_bbox[net_name][2], term['rect'][2])
                    pin_bbox[net_name][3] = max(pin_bbox[net_name][3], term['rect'][3])

        placement_data['leaves'].append({
            'abstract_name': leaf['abstract_template_name'],
            'concrete_name': leaf['concrete_template_name'],
            'constraints': leaf['constraints'],
            'bbox': leaf['bbox'],
            'terminals': leaf['terminals'],
            'pin_bbox': pin_bbox})

    modules = {module['name']: module for module in input_data['modules']}
    topological_order, found_modules, _ = compute_topoorder(modules, top_level)

    # Propagate power pins down the modules
    if global_signals := {x['actual'] for x in input_data['global_signals']}:
        propagate_down_global_signals(modules, top_level, global_signals)

    for name in topological_order:
        if name not in found_modules:
            continue

        # Select and call placement algorithm here
        print(f'Placing {name}')
        place_using_sequence_pairs(placement_data, modules[name], top_level)

    check_placement(VerilogJsonTop.parse_obj(placement_data), scale_factor)

    # Trim unused modules and leaves
    placement_data = trim_placement_data(placement_data, top_level)

    return placement_data

def draw_placement(placement_data, module_name):
    leaves = {x['concrete_name']: x for x in placement_data['leaves']}
    modules = {x['concrete_name']: x for x in placement_data['modules']}
    module = modules[module_name]

    colorscale = px.colors.qualitative.Alphabet

    fig = go.Figure()
    fig.update_xaxes(range=[0, max(module['bbox'])])
    fig.update_yaxes(range=[0, max(module['bbox'])])

    # Add shapes
    x_lst = list()
    y_lst = list()
    n_lst = list()

    i = 0
    for instance in module['instances']:
        concrete_name = instance['concrete_template_name']

        if concrete_name in leaves:
            bbox = leaves[concrete_name]['bbox']
        elif concrete_name in modules:
            bbox = modules[concrete_name]['bbox']
        else:
            assert False

        bbox = Transformation( instance['transformation']['oX'], instance['transformation']['oY'],
            instance['transformation']['sX'], instance['transformation']['sY']).hitRect(Rect(*bbox)).canonical().toList()

        llx, lly, urx, ury = bbox

        color = colorscale[i % len(colorscale)]
        fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="RoyalBlue", width=3), fillcolor=color)
        i += 1
        x_lst.append((llx+urx)/2)
        y_lst.append((lly+ury)/2)
        n_lst.append(f"{instance['instance_name']}")

    fig.update_shapes(opacity=0.5, xref="x", yref="y")

    # Add labels
    fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=n_lst, mode="text", textfont=dict(color="black", size=24)))

    fig.show()


def placer_wrapper(verilog, top, vmap, inputs, output, draw):
    with open(verilog, 'r') as fp:
        input_data = json.load(fp)
    with open(vmap, 'r') as fp:
        lines = fp.readlines()
        for line in lines:
            line = line.split()
            ln = line[1].replace(".gds", "")
            with open(f'{inputs}/{ln}.json', 'r') as fp1:
                leaf_json = json.load(fp1)
                leaf_data = {'abstract_template_name':line[0], 'concrete_template_name':ln}
                leaf_data['bbox'] = leaf_json['bbox'] if 'bbox' in leaf_json else None
                leaf_data['terminals'] = [t for t in leaf_json['terminals'] if t['netType'] == 'pin'] if 'terminals' in leaf_json else None
                leaf_data['constraints'] = []
                if 'leaves' not in input_data:
                    input_data['leaves'] = []
                input_data['leaves'].append(leaf_data)
    
    #with open('placement_input.json', "wt") as fp:
    #    fp.write(json.dumps(input_data, indent=2) + '\n')
    placement_data = pythonic_placer(top, input_data)
    placement_data = trim_placement_data(placement_data, top)
    with open(output, "wt") as fp:
        json.dump(placement_data, fp=fp, indent=2)
    if draw: draw_placement(placement_data, f'{top}_0')

if __name__ == '__main__':
  import argparse
  ap = argparse.ArgumentParser()
  ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
  ap.add_argument( "-t", "--top", type=str, default="", help='<top module name>')
  ap.add_argument( "-m", "--map", type=str, default="", help='<map file in the 3_pnr/inputs directory>')
  ap.add_argument( "-i", "--inputs", type=str, default="3_pnr/inputs", help='<path of 3_pnr/inputs directory>')
  ap.add_argument( "-o", "--output", type=str, default="placement_output.json", help='<output placement file>')
  ap.add_argument( "-d", "--draw", action='store_true', help='<draw layout on browser canvas>')
  args = ap.parse_args()
  print(f"verilog file : {args.verilog}")
  print(f"map file     : {args.map}")
  print(f"top module   : {args.top}")
  print(f"input dir    : {args.inputs}")
  print(f"output       : {args.output}")
  if args.verilog == "" or args.inputs == "" or args.map == "" or args.top == "":
      ap.print_help()
      exit()
  placer_wrapper(args.verilog, args.top, args.map, args.inputs, args.output, args.draw)
