import mip
import time
import copy
import itertools
import more_itertools
import networkx as nx
from collections import defaultdict

import align.schema.constraint as constraint_schema
from align.schema.hacks import VerilogJsonTop
from align.pnr.grid_constraints import gen_constraints_for_module
from align.cell_fabric.transformation import Transformation, Rect


class HyperParameters:
    max_sequence_pairs = 100
    max_block_variants = 100
    max_candidates = 10000
    max_solutions = 1


def check_place_on_grid(instance, constraints):
    for const in constraints:

        if const['constraint'] != 'PlaceOnGrid':
            continue

        axis = 'Y' if const['direction'] == 'H' else 'X'
        o, s = instance['transformation'][f'o{axis}'], instance['transformation'][f's{axis}']

        is_satisfied = False
        for term in const['ored_terms']:
            for offset in term['offsets']:
                if (o - offset) % const['pitch'] == 0 and s in term['scalings']:
                    is_satisfied = True
                    break
            if is_satisfied:
                break
        assert is_satisfied, f'{instance} does not satisfy {const}'


def measure_time(func):
    def wrapper(*args, **kwargs):
        s = time.time()
        returned_value = func(*args, **kwargs)
        e = time.time() - s
        print(f'Elapsed time: {e:.3f} secs')
        return returned_value
    return wrapper


def enumerate_sequence_pairs(constraints, instance_map: dict, max_sequences: int):

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
            if count > max_sequences:
                break
        if count > max_sequences:
            break

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


def place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=None, place_on_grid=None):

    model = mip.Model(sense=mip.MINIMIZE, solver_name=mip.CBC)
    model.verbose = 0  # set to one to see more progress output with the solver

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
        model += model.var_by_name(f'{name}_urx') - model.var_by_name(f'{name}_llx') == size['x']
        model += model.var_by_name(f'{name}_ury') - model.var_by_name(f'{name}_lly') == size['y']

        # All instances within the bounding box
        model += model.var_by_name(f'{name}_urx') <= model.var_by_name('W')
        model += model.var_by_name(f'{name}_ury') <= model.var_by_name('H')

        # PlaceOnGrid constraints
        if place_on_grid and name in place_on_grid:
            assert len(place_on_grid[name]) <= 2
            for constraint in place_on_grid[name]:
                axis = 'y' if constraint['direction'] == 'H' else 'x'
                pitch = constraint['pitch']
                flip = model.var_by_name(f'{name}_f{axis}')

                offset_scalings = defaultdict(list)
                offset_variables = list()
                for term in constraint['ored_terms']:
                    offsets = term['offsets']
                    scalings = term['scalings']
                    assert set(scalings) in [{1}, {-1}, {-1, 1}]
                    for offset in offsets:
                        offset_scalings[offset].extend(scalings)

                for offset, scalings in offset_scalings.items():
                    var = model.add_var(var_type=mip.BINARY)
                    offset_variables.append((offset, var))
                    if set(scalings) == {1}:
                        model += var + flip <= 1
                    elif set(scalings) == {-1}:
                        model += var <= flip

                model += mip.xsum(var[1] for var in offset_variables) == 1
                grid = model.add_var(name=f'{name}_grid_{axis}', var_type=mip.INTEGER, lb=0)
                origin = grid*pitch + mip.xsum(v[0]*v[1] for v in offset_variables)
                model += origin - size[axis] * flip == model.var_by_name(f'{name}_ll{axis}')

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
                    model += eqn <= model.var_by_name(f'{wire_name}_ur{axis}')
                    model += model.var_by_name(f'{wire_name}_ll{axis}') <= eqn

        model += \
            mip.xsum(model.var_by_name(f'{wire_name}_ur{axis}') for wire_name in wires for axis in ['x', 'y']) - \
            mip.xsum(model.var_by_name(f'{wire_name}_ll{axis}') for wire_name in wires for axis in ['x', 'y']) == model.var_by_name('HPWL')

    else:
        model += model.var_by_name('HPWL') == 0

    # Constraints implied by the sequence pairs
    reverse_map = {v: k for k, v in instance_map.items()}
    instance_pos = {reverse_map[index]: i for i, index in enumerate(sequence_pair[0])}
    instance_neg = {reverse_map[index]: i for i, index in enumerate(sequence_pair[1])}
    for index0, index1 in itertools.combinations(reverse_map, 2):
        name0 = reverse_map[index0]
        name1 = reverse_map[index1]
        assert name0 != name1
        if instance_pos[name0] < instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:    # bb = LEFT
            model += model.var_by_name(f'{name0}_urx') <= model.var_by_name(f'{name1}_llx')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # aa = RIGHT
            model += model.var_by_name(f'{name1}_urx') <= model.var_by_name(f'{name0}_llx')
        elif instance_pos[name0] < instance_pos[name1] and instance_neg[name0] > instance_neg[name1]:  # ba = ABOVE
            model += model.var_by_name(f'{name1}_ury') <= model.var_by_name(f'{name0}_lly')
        elif instance_pos[name0] > instance_pos[name1] and instance_neg[name0] < instance_neg[name1]:  # ab = BELOW
            model += model.var_by_name(f'{name0}_ury') <= model.var_by_name(f'{name1}_lly')
        else:
            assert False

    # Placement constraints
    for constraint in constraints:

        if isinstance(constraint, constraint_schema.Boundary):
            if max_width := getattr(constraint, 'max_width', False):
                model += model.var_by_name('W') <= max_width
            if max_height := getattr(constraint, 'max_height', False):
                model += model.var_by_name('H') <= max_height

        if isinstance(constraint, constraint_schema.PlaceOnBoundary):
            for name in constraint.instances_on(['north', 'northwest', 'northeast']):
                model += model.var_by_name(f'{name}_ury') == model.var_by_name('H')
            for name in constraint.instances_on(['south', 'southwest', 'southeast']):
                model += model.var_by_name(f'{name}_lly') == 0
            for name in constraint.instances_on(['east', 'northeast', 'southeast']):
                model += model.var_by_name(f'{name}_urx') == model.var_by_name('W')
            for name in constraint.instances_on(['west', 'northwest', 'southwest']):
                model += model.var_by_name(f'{name}_llx') == 0

        # TODO: Placement constraints except Order (sequence pair already satisfies order)

    # Minimize the perimeter of the bounding box
    model.objective += model.var_by_name('W') + model.var_by_name('H') + model.var_by_name('HPWL')

    model.write('model.lp')

    # Solve
    status = model.optimize(max_seconds_same_incumbent=60.0, max_seconds=300)
    if status == mip.OptimizationStatus.OPTIMAL:
        print(f'optimal solution found: cost={model.objective_value}')
    elif status == mip.OptimizationStatus.FEASIBLE:
        print(f'solution with cost {model.objective_value} current lower bound: {model.objective_bound}')
    else:
        print('No solution to ILP')
        return False

    # if status == mip.OptimizationStatus.OPTIMAL or status == mip.OptimizationStatus.FEASIBLE:
    #     if model.verbose:
    #         print('Solution:')
    #         for v in model.vars:
    #             print('\t', v.name, v.x)
    #         print(f'Number of solutions: {model.num_solutions}')

    # Extract solution
    transformations = dict()
    for name, _ in instance_map.items():
        fx, fy = model.var_by_name(f'{name}_fx').x, model.var_by_name(f'{name}_fy').x
        ox = model.var_by_name(f'{name}_llx').x + fx * instance_sizes[name][0]
        oy = model.var_by_name(f'{name}_lly').x + fy * instance_sizes[name][1]
        sx = 1 if fx == 0 else -1
        sy = 1 if fy == 0 else -1
        transformations[name] = {'oX': int(ox), 'oY': int(oy), 'sX': sx, 'sY': sy}

    w = int(model.var_by_name('W').x)
    h = int(model.var_by_name('H').x)
    solution = {
        'cost': model.objective.x,
        'width': w,
        'height': h,
        'area': w*h,
        'hpwl': model.var_by_name('HPWL').x,
        'transformations': transformations,
        'model': model
    }
    return solution


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

    reverse_instance_map = {v: k for k, v in instance_map.items()}

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
    for block_variant, sequence_pair in itertools.islice(itertools.product(block_variants, sequence_pairs), hyper_params.max_candidates):
        instance_sizes = dict()
        place_on_grid = dict()
        wires = defaultdict(list)
        for idx, selected in enumerate(block_variant):
            instance_name = reverse_instance_map[idx]
            concrete_template = variant_map[instances[instance_name][ATN]][selected]
            bbox = concrete_template['bbox']
            instance_sizes[instance_name] = [bbox[2] - bbox[0], bbox[3] - bbox[1]]
            place_on_grid[instance_name] = [c for c in concrete_template.get('constraints', list()) if c['constraint'] == 'PlaceOnGrid']

            for formal_actual in instances[instance_name]['fa_map']:
                formal, actual = formal_actual['formal'], formal_actual['actual']
                if actual not in module['global_signals']:
                    wires[actual].append((instance_name, tuple(x for x in concrete_template['pin_bbox'][formal])))

        solution = place_sequence_pair(constraints, instance_map, instance_sizes, sequence_pair, wires=wires, place_on_grid=place_on_grid)
        if solution:
            solution['sequence_pair'] = sequence_pair
            solution['block_variant'] = block_variant
            solutions.append(solution)

    assert solutions, f'No placement solution found for {module}'

    # Annotate best K solutions to placement_data
    solutions.sort(key=lambda x: x['cost'])

    max_solutions = hyper_params.max_solutions if module['name'] == top_level else 1

    for i in range(max_solutions):
        solution = solutions[i]
        new_module = copy.deepcopy(module)
        pin_bbox = dict()
        for instance in new_module['instances']:
            instance_name = instance['instance_name']
            instance['transformation'] = solution['transformations'][instance_name]
            variant_index = solution['block_variant'][instance_map[instance_name]]
            concrete_template = variant_map[instance[ATN]][variant_index]
            instance[CTN] = concrete_template['concrete_name']
            check_place_on_grid(instance, concrete_template['constraints'])

            # Annotate bounding box of pins to the module
            for formal_actual in instance['fa_map']:
                formal, actual = formal_actual['formal'], formal_actual['actual']
                if actual not in module['global_signals']:
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
