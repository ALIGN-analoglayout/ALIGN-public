import z3
import time
import pytest
import itertools
import more_itertools

POS = "pos"
NEG = "neg"
LLX = "llx"
URX = "urx"
LLY = "lly"
URY = "ury"
SEP = "___"
NUM_SOLUTIONS = 1


def define_vars(instances):
    block_vars = dict()
    for b in instances:
        block_vars[b] = dict()
        block_vars[b][POS] = z3.Int(f"{POS}{SEP}{b}")
        block_vars[b][NEG] = z3.Int(f"{NEG}{SEP}{b}")
        for x in [LLX, URX, LLY, URY]:
            block_vars[b][x] = z3.Int(f"{x}{SEP}{b}")
    return block_vars


def default_constraints(block_vars, solver):
    num_blocks = len(block_vars)

    # Restrict range of each variable
    for b, d in block_vars.items():
        solver.add(z3.And(d[POS] > 0, d[POS] <= num_blocks))
        solver.add(z3.And(d[NEG] > 0, d[NEG] <= num_blocks))
        for x in [LLX, URX, LLY, URY]:
            solver.add(d[x] >= 0)
        solver.add(z3.And(d[URX] > d[LLX], d[URY] > d[LLY]))

    # Two blocks cannot occupy the same index nor overlap
    blocks = [b for b in block_vars.keys()]
    for i, j in itertools.combinations(blocks, 2):
        a = block_vars[i]
        b = block_vars[j]
        solver.add(a[POS] != b[POS])
        solver.add(a[NEG] != b[NEG])
        solver.add(z3.Or(
                a[URX] <= b[LLX],
                b[URX] <= a[LLX],
                a[URY] <= b[LLY],
                b[URY] <= a[LLY]
            ))


def find_solution(solver):
    # Solve
    # s = time.time()
    r = solver.check()
    # e = time.time()
    # print(f"Elapsed time: {e-s:0.3f} seconds")
    # print(solver)
    if r == z3.sat:
        m = solver.model()

        seq_pos = [(b, m[b]) for b in m if str(b).startswith("pos")]
        seq_neg = [(b, m[b]) for b in m if str(b).startswith("neg")]

        seq_pos = sorted(seq_pos, key=lambda x: x[1].as_long())
        seq_neg = sorted(seq_neg, key=lambda x: x[1].as_long())

        seq_pos = [str(b[0]).split(SEP)[1] for b in seq_pos]
        seq_neg = [str(b[0]).split(SEP)[1] for b in seq_neg]

        seq_pos = " ".join(seq_pos)
        seq_neg = " ".join(seq_neg)

        # print(sorted([(d, m[d]) for d in m], key=lambda x: str(x[0])))
        sequence_pair = f"{seq_pos},{seq_neg}"
        # print(f"{sequence_pair=}")
        return sequence_pair
    else:
        return False


def not_a_left_of_b(a, b):
    return z3.Not(z3.And(a[POS] < b[POS], a[NEG] < b[NEG]))


def not_a_right_of_b(a, b):
    return z3.Not(z3.And(a[POS] > b[POS], a[NEG] > b[NEG]))


def not_a_above_b(a, b):
    return z3.Not(z3.And(a[POS] < b[POS], a[NEG] > b[NEG]))


def not_a_below_b(a, b):
    return z3.Not(z3.And(a[POS] > b[POS], a[NEG] < b[NEG]))


def order(a, b, axis, abut=False):
    expression = list()
    if axis == 'h':  # left to right
        expression.append(not_a_right_of_b(a, b))
        if abut:
            expression.append(a[URX] == b[LLX])
        else:
            expression.append(a[URX] <= b[LLX])
    else:  # bottom to top
        expression.append(not_a_below_b(a, b))
        if abut:
            expression.append(a[URY] == b[LLY])
        else:
            expression.append(a[URY] <= b[LLY])
    return z3.And(*expression)


def align(a, b, axis):
    expression = list()
    if axis == 'h':
        expression.append(z3.Or(
            z3.And(a[POS] > b[POS], a[NEG] > b[NEG]),
            z3.And(a[POS] < b[POS], a[NEG] < b[NEG])
        ))
        # a and b should align horizontally
        expression.append(a[LLY] == b[LLY])
    else:
        expression.append(z3.Or(
            z3.And(a[POS] > b[POS], a[NEG] < b[NEG]),
            z3.And(a[POS] < b[POS], a[NEG] > b[NEG])
        ))
        # a and b should align vertically
        expression.append(a[LLX] == b[LLX])
    return z3.And(*expression)


def generate_sequence_pair(constraints, solver, n=NUM_SOLUTIONS, additional_instances=None):

    # Collect instances
    instances = list()
    for const in constraints:
        if const["constraint"] == "SymmetricBlocks":
            assert const["direction"] == "V", f"Not implemented yet: {const}"
            for p in const["pairs"]:
                instances.extend(p)
        elif const["constraint"] in ["Align", "Order", "SameTemplate"]:
            instances.extend(const["instances"])
            if const["constraint"] == "Align":
                assert const["direction"] in ["h_bottom", "v_left"], f"Not implemented yet: {const}"
        elif const["constraint"] == "PlaceOnBoundary":
            # for schema verify that all of the below are disjoint
            for attr in ["north", "south", "east", "west", "northeast", "northwest", "southeast", "southwest"]:
                if const.get(attr, False):
                    if isinstance(const[attr], list):
                        instances.extend(const[attr])
                    else:
                        instances.append(const[attr])
        else:
            assert False, f"Not implemented yet: {const}"

    if additional_instances:
        instances.extend(additional_instances)
    assert instances

    instances = set(sorted(instances))
    num_blocks = len(instances)
    print(f"{num_blocks=} {len(constraints)=}")
    block_vars = define_vars(instances)

    default_constraints(block_vars, solver)

    # Constraints due to symmetric blocks
    for const in constraints:
        if const["constraint"] == "SymmetricBlocks":
            symm_self = list()
            symm_pair = list()
            for p in const['pairs']:
                if len(p) == 2:
                    symm_pair.append(p)
                else:
                    symm_self.extend(p)

            for p in symm_pair:
                a = block_vars[p[0]]
                b = block_vars[p[1]]
                # a and b should align along the axis
                solver.add(align(a, b, 'h'))

            for p in itertools.combinations(symm_self, 2):
                a = block_vars[p[0]]
                b = block_vars[p[1]]
                # a is either above or below b
                solver.add(z3.Or(order(a, b, 'v'), order(b, a, 'v')))
                # centerlines should match
                solver.add(a[LLX] + a[URX] == b[LLX] + b[URX])

            for i in symm_self:
                s = block_vars[i]
                for j, k in symm_pair:
                    a = block_vars[j]
                    b = block_vars[k]
                    solver.add(z3.Or(
                        z3.And(order(a, s, 'h'), order(s, b, 'h')),
                        z3.And(order(b, s, 'h'), order(s, a, 'h')),
                        z3.And(order(s, a, 'v'), order(s, b, 'v')),
                        z3.And(order(a, s, 'v'), order(b, s, 'v'))
                    ))
                # centerlines should match
                solver.add(a[LLX] + a[URX] + b[LLX] + b[URX] == 2*s[LLX] + 2*s[URX])

            # blocks in two separate pairs should not conflict
            for p in itertools.combinations(symm_pair, 2):
                a = block_vars[p[0][0]]
                b = block_vars[p[0][1]]
                c = block_vars[p[1][0]]
                d = block_vars[p[1][1]]
                # [a,b], [c,d]: a,b cannot be left of c,d
                solver.add(z3.Not(z3.And(
                    order(a, c, 'h'),
                    order(a, d, 'h'),
                    order(b, c, 'h'),
                    order(b, d, 'h')
                    )))
                # [a,b], [c,d]: a,b cannot be right of c,d
                solver.add(z3.Not(z3.And(
                    order(c, a, 'h'),
                    order(d, a, 'h'),
                    order(c, b, 'h'),
                    order(d, b, 'h')
                    )))

        elif const["constraint"] == "Order":
            abut = True if "abut" in const and const["abut"] else False
            for i, j in more_itertools.pairwise(const["instances"]):
                a = block_vars[i]
                b = block_vars[j]
                if const["direction"] == "top_to_bottom":
                    solver.add(order(a, b, "v", abut=abut))
                elif const["direction"] == "left_to_right":
                    solver.add(order(a, b, "h", abut=abut))
                else:
                    assert False

        elif const["constraint"] == "Align":
            for i, j in itertools.combinations(const["instances"], 2):
                a = block_vars[i]
                b = block_vars[j]
                if const["direction"] == "h_bottom":
                    solver.add(align(a, b, "h"))
                elif const["direction"] == "v_left":
                    solver.add(align(a, b, "v"))
                else:
                    assert False

        elif const["constraint"] == "PlaceOnBoundary":

            def find_instances_on(lst):
                sublist = list()
                for attr in lst:
                    if const.get(attr, False):
                        if isinstance(const[attr], list):
                            sublist.extend(const[attr])
                        else:
                            sublist.append(const[attr])
                return sublist

            all_north = find_instances_on(["north", "northwest", "northeast"])
            for i, j in itertools.combinations(all_north, 2):
                a = block_vars[i]
                b = block_vars[j]
                solver.add(not_a_below_b(a, b))
                solver.add(not_a_above_b(a, b))

            all_south = find_instances_on(["south", "southwest", "southeast"])
            for i, j in itertools.combinations(all_south, 2):
                a = block_vars[i]
                b = block_vars[j]
                solver.add(not_a_below_b(a, b))
                solver.add(not_a_above_b(a, b))

            all_west = find_instances_on(["west", "southwest", "northwest"])
            for i, j in itertools.combinations(all_west, 2):
                a = block_vars[i]
                b = block_vars[j]
                solver.add(not_a_left_of_b(a, b))
                solver.add(not_a_right_of_b(a, b))

            all_east = find_instances_on(["east", "southeast", "northeast"])
            for i, j in itertools.combinations(all_east, 2):
                a = block_vars[i]
                b = block_vars[j]
                solver.add(not_a_left_of_b(a, b))
                solver.add(not_a_right_of_b(a, b))

            for i in instances:
                b = block_vars[i]

                if const.get("northwest") and const["northwest"] != i:
                    a = block_vars[const["northwest"]]
                    solver.add(a[URY] >= b[URY])
                    solver.add(a[LLX] <= b[LLX])
                    solver.add(not_a_right_of_b(a, b))
                    solver.add(not_a_below_b(a, b))

                if const.get("northeast") and const["northeast"] != i:
                    a = block_vars[const["northeast"]]
                    solver.add(a[URY] >= b[URY])
                    solver.add(a[URX] >= b[URX])
                    solver.add(not_a_left_of_b(a, b))
                    solver.add(not_a_below_b(a, b))

                if const.get("southwest") and const["southwest"] != i:
                    a = block_vars[const["southwest"]]
                    solver.add(a[LLY] <= b[LLY])
                    solver.add(a[LLX] <= b[LLX])
                    solver.add(not_a_right_of_b(a, b))
                    solver.add(not_a_above_b(a, b))

                if const.get("southeast") and const["southeast"] != i:
                    a = block_vars[const["southeast"]]
                    solver.add(a[LLY] <= b[LLY])
                    solver.add(a[URX] >= b[URX])
                    solver.add(not_a_left_of_b(a, b))
                    solver.add(not_a_above_b(a, b))

                if const.get("north") and (i not in const["north"]):
                    for block in const["north"]:
                        a = block_vars[block]
                        solver.add(a[URY] >= b[URY])
                        solver.add(not_a_below_b(a, b))

                if const.get("south") and (i not in const["south"]):
                    for block in const["south"]:
                        a = block_vars[block]
                        solver.add(a[LLY] <= b[LLY])
                        solver.add(not_a_above_b(a, b))

                if const.get("east") and (i not in const["east"]):
                    for block in const["east"]:
                        a = block_vars[block]
                        solver.add(a[URX] >= b[URX])
                        solver.add(not_a_left_of_b(a, b))

                if const.get("west") and (i not in const["west"]):
                    for block in const["west"]:
                        a = block_vars[block]
                        solver.add(a[LLX] <= b[LLX])
                        solver.add(not_a_right_of_b(a, b))

    initial_pair = find_solution(solver)
    if n < 2 or not initial_pair:
        return initial_pair
    else:
        m = solver.model()
        previous_solution = {str(p): m[p].as_long() for p in m}
        sequence_pairs = [initial_pair]
        for i in range(n-1):

            clauses = []
            for b in block_vars:
                for SEQ in [POS, NEG]:
                    bvar = block_vars[b][SEQ]
                    clauses.append(bvar == previous_solution[str(bvar)])

            # print(z3.Not(z3.And(*clauses)))
            # assert False
            solver.add(z3.Not(z3.And(*clauses)))
            # print(solver)

            if new_solution := find_solution(solver):
                sequence_pairs.append(new_solution)
                m = solver.model()
                previous_solution = {str(p): m[p].as_long() for p in m}
            else:
                break

        print(f"{n=} {len(sequence_pairs)=}")

        return sequence_pairs


def test_order():
    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 1"

    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "c"], "abut": True},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 2"

    constraints = [
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "a"], "abut": True},
        ]
    # Legal solution: bca, abc
    #  |a
    # b|
    #  |c
    assert generate_sequence_pair(constraints, z3.Solver()), "case 3"

    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["a", "b"]},
        ]
    # Legal solution: ba, ab
    # a|
    #  |b
    assert generate_sequence_pair(constraints, z3.Solver()), "case 4"


def test_align():
    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "v_left",   "instances": ["b", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 1"

    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "h_bottom", "instances": ["b", "c"]},
        {"constraint": "Align", "direction": "v_left",   "instances": ["a", "c"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 2"

    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["b", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 3"


def test_symmetry():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["a", "b"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 1"

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "b", "a"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 2"

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "c", "b"]},
    ]
    assert generate_sequence_pair(constraints, z3.Solver()), "case 3"

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Align", "direction": "v_left", "instances": ["b", "a"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver()), "case 4"


def test_align_symmetry():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"]]},
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "c"]},
        {"constraint": "Align", "direction": "v_left",   "instances": ["b", "c"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver())


def test_1():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs":
            [["a", "b"], ["c", "d"], ["e"], ["f"], ["g", "h"], ["m", "n"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["f", "a", "c", "g", "m", "e"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "d"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["g", "h"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["m", "n"]}
        ]
    assert generate_sequence_pair(constraints, z3.Solver())


def test_2():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs":
            [["a", "b"], ["c", "d"], ["e"], ["f"], ["g", "h"], ["m", "n"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["f", "a", "c", "g", "m", "e"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "d"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["g", "h"], "abut": True},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["m", "n"]},
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b", "o", "p"]},
        {"constraint": "Align", "direction": "v_left", "instances": ["c", "g", "r"]}
        ]
    assert generate_sequence_pair(constraints, z3.Solver())


def test_3():
    constraints = [
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPTAIL']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPPBIAS']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PULLUP_ENB']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PBIAS_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES0', 'X_XDECAP_NZ3']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES1', 'X_XDECAP_NZ3']},
    ]
    assert generate_sequence_pair(constraints, z3.Solver())


def test_4():
    constraints = [
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPTAIL']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XPPBIAS']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PULLUP_ENB']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XDECAP_P', 'X_XSW_PBIAS_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPTAIL', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XP2', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XPPBIAS', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLUP_ENB', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_DP_XPINP_XPINN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XINVP2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PBIAS_EN', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP1', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVP2', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_CM_XNLDL_XNLDR']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XSW_PULLDN_EN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XMP_TIE_HI', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_CM_XNLDL_XNLDR', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XSW_PULLDN_EN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN1', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES0']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XINVN2', 'X_XNRES1']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES0', 'X_XDECAP_NZ3']},
        {'abut': False, 'constraint': 'Order', 'direction': 'top_to_bottom', 'instances': ['X_XNRES1', 'X_XDECAP_NZ3']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XPTAIL', 'X_XP2', 'X_XPPBIAS', 'X_XSW_PULLUP_ENB', 'X_XSW_PBIAS_EN']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_DP_XPINP_XPINN', 'X_XINVP1', 'X_XINVP2', 'X_XMP_TIE_HI']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XSW_PULLDN_EN', 'X_CM_XNLDL_XNLDR', 'X_XSW_PULLDN_EN1', 'X_XN2', 'X_XINVN1', 'X_XINVN2']},
        {'abut': False, 'constraint': 'Order', 'direction': 'left_to_right', 'instances': ['X_XNRES0', 'X_XNRES1']},
        {'constraint': 'SymmetricBlocks', 'direction': 'V', 'pairs': [['X_XPTAIL'], ['X_DP_XPINP_XPINN'], ['X_CM_XNLDL_XNLDR'], ['X_XSW_PULLDN_EN', 'X_XSW_PULLDN_EN1']]},
    ]
    assert generate_sequence_pair(constraints, z3.Solver())


def test_variants_sanity():
    for abc in itertools.permutations("abc"):
        constraints = [
            {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b", "c"]},
            {"constraint": "Order", "direction": "left_to_right", "instances": abc},
        ]
        assert generate_sequence_pair(constraints, z3.Solver(), n=24)


def test_variants():
    constraints = [{"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]}]
    s = time.time()
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=24)
    e = time.time()
    print(f"{len(sequence_pairs)} variants generated in {e-s:0.3f} seconds")
    for p in sequence_pairs:
        print(p)
    assert len(sequence_pairs) == 2


def test_boundary():
    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "x"}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10, additional_instances=["y"])
    assert set(sequence_pairs) == {'x y,x y', 'x y,y x'}

    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "x", "northeast": "y"}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10, additional_instances=["x", "y"])
    assert set(sequence_pairs) == {'x y,x y'}

    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "a", "northeast": "b", "southwest": "c", "southeast": "d"}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10)
    assert len(sequence_pairs) == 4

    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "a", "north": ["b"]}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10)
    assert len(sequence_pairs) == 1

    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "a", "north": ["b", "c"], "northeast": "d"}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10)
    assert len(sequence_pairs) == 2

    constraints = [{"constraint": "PlaceOnBoundary", "northwest": "a", "north": ["b", "c"]}]
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=10)
    assert len(sequence_pairs) == 2

    # constraints = [{"constraint": "PlaceOnBoundary", "northwest": "a", "northeast": "b", "southwest": "c", "southeast": "d"}]
    # s = time.time()
    # sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=1000, additional_instances=["e", "f"])
    # e = time.time()
    # print(f"{len(sequence_pairs)} variants generated in {e-s:0.3f} seconds")
    # assert sequence_pairs


@pytest.mark.skip()
def test_runtime():
    constraints = [{"constraint": "SameTemplate", "instances": ["a", "b", "c", "d", "e"]}]
    s = time.time()
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=1000)
    e = time.time()
    print(f"{len(sequence_pairs)} variants generated in {e-s:0.3f} seconds")
