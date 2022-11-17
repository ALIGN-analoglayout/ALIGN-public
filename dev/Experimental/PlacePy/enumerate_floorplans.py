import itertools
import more_itertools
import networkx as nx
import align.schema.constraint as constraint_schema


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
            sequence_pairs.append((pos, neg))
            count += 1
            if count > max_sequences:
                break
        if count > max_sequences:
            break

    return sequence_pairs


def enumerate_variants(constraints, instance_map: dict, variant_counts: dict, max_variants: int):

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
        variants.append(selection)
        if count > max_variants:
            break
    return variants


# Tests
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context


def initialize_constraints(n):
    library = Library()
    with set_context(library):
        model = Model(name='TwoTerminalDevice', pins=['A', 'B'], parameters={})
        library.append(model)
        subckt = SubCircuit(name='SUBCKT', pins=['PIN1', 'PIN2'], parameters={})
        library.append(subckt)
    with set_context(subckt.elements):
        for i in range(n):
            subckt.elements.append(Instance(name=f'M{i}', model='TwoTerminalDevice', pins={'A': 'PIN1', 'B': 'PIN2'}))
    instance_map = {f'M{i}': i for i in range(n)}
    return subckt.constraints, instance_map


def test_enumerate_sequence_pairs():

    constraints, instance_map = initialize_constraints(2)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 100)
    assert len(sequence_pairs) == 4

    constraints, instance_map = initialize_constraints(4)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 576

    constraints, instance_map = initialize_constraints(20)
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1000

    constraints, instance_map = initialize_constraints(4)
    with set_context(constraints):
        constraints.append(constraint_schema.Order(direction='left_to_right', instances=[f'M{i}' for i in range(4)]))
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1
    assert sequence_pairs[0] == ([0, 1, 2, 3], [0, 1, 2, 3])

    constraints, instance_map = initialize_constraints(4)
    with set_context(constraints):
        constraints.append(constraint_schema.Order(direction='top_to_bottom', instances=[f'M{i}' for i in range(4)]))
    sequence_pairs = enumerate_sequence_pairs(constraints, instance_map, 1000)
    assert len(sequence_pairs) == 1
    assert sequence_pairs[0] == ([0, 1, 2, 3], [3, 2, 1, 0])


def test_enumerate_variants():

    constraints, instance_map = initialize_constraints(2)
    variant_counts = {"M0": 4, "M1": 5}
    variants = enumerate_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 20

    constraints, instance_map = initialize_constraints(4)
    variant_counts = {k: 2 for k in instance_map.keys()}
    with set_context(constraints):
        constraints.append(constraint_schema.SameTemplate(instances=[f'M{i}' for i in range(4)]))
    variants = enumerate_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 2
    assert variants == [[0]*4, [1]*4]

    constraints, instance_map = initialize_constraints(4)
    variant_counts = {k: 3 for k in instance_map.keys()}
    with set_context(constraints):
        constraints.append(constraint_schema.SameTemplate(instances=["M1", "M2"]))
        constraints.append(constraint_schema.SameTemplate(instances=["M2", "M3"]))
    variants = enumerate_variants(constraints, instance_map, variant_counts, 100)
    assert len(variants) == 3*3
