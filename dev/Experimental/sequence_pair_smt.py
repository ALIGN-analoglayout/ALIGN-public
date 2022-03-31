import z3
import time
import itertools
import more_itertools


POS = "pos"
NEG = "neg"
SEP = "___"


def define_vars(block_vars, b):
    if b not in block_vars:
        block_vars[b] = dict()
        block_vars[b][POS] = z3.Int(f"{POS}{SEP}{b}")
        block_vars[b][NEG] = z3.Int(f"{NEG}{SEP}{b}")


def find_solution(solver):
    # Solve
    s = time.time()
    r = solver.check()
    e = time.time()
    print(f"Elapsed time: {e-s:0.3f} seconds")
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
        print(f"{sequence_pair=}")
        return sequence_pair
    else:
        return False


def merge_align_constraints(constraints):

    h_groups = []
    v_groups = []
    merged_constraints = list()
    for const in constraints:
        if const["constraint"] == "Align":
            if const["direction"] == "h_bottom":
                if not h_groups:
                    h_groups.append(set(const['instances']))
                else:
                    group_exists = False
                    inst_set = set(const['instances'])
                    for i, hg in enumerate(h_groups):
                        if set.intersection(hg, inst_set):
                            group_exists = True
                            break
                    if group_exists:
                        h_groups[i] = set.union(h_groups[i], inst_set)
                    else:
                        h_groups.append(inst_set)
            else:
                if not v_groups:
                    v_groups.append(set(const['instances']))
                else:
                    group_exists = False
                    inst_set = set(const['instances'])
                    for i, vg in enumerate(v_groups):
                        if set.intersection(vg, inst_set):
                            group_exists = True
                            break
                    if group_exists:
                        v_groups[i] = set.union(v_groups[i], inst_set)
                    else:
                        v_groups.append(inst_set)

        else:
            merged_constraints.append(const)

    for hg in h_groups:
        const = {"constraint": "Align", "direction": "h_bottom", "instances": sorted(list(hg))}
        merged_constraints.append(const)

    for vg in v_groups:
        const = {"constraint": "Align", "direction": "v_left", "instances": sorted(list(vg))}
        merged_constraints.append(const)

    return(merged_constraints)


def generate_sequence_pair(constraints, solver, n=10):
    block_vars = dict()

    # Define variables for each block
    for const in constraints:
        if const["constraint"] == "SymmetricBlocks":
            assert const["direction"] == "V", f"Not implemented yet: {const}"
            for p in const["pairs"]:
                for b in p:
                    define_vars(block_vars, b)
        elif const["constraint"] in ["Align", "Order"]:
            for i in const["instances"]:
                define_vars(block_vars, i)
            if const["constraint"] == "Align":
                assert const["direction"] in ["h_bottom", "v_left"], f"Not implemented yet: {const}"
        else:
            assert False, f"Not implemented yet: {const}"

    constraints = merge_align_constraints(constraints)

    num_blocks = len(block_vars)
    # print(block_vars)
    print(f"{num_blocks=} {len(constraints)=}")

    # Restrict range of each variable
    for b, d in block_vars.items():
        solver.add(z3.And(d[POS] > 0, d[POS] <= num_blocks))
        solver.add(z3.And(d[NEG] > 0, d[NEG] <= num_blocks))

    # Two blocks cannot occupy the same index
    blocks = [b for b in block_vars.keys()]

    for i, j in itertools.combinations(blocks, 2):
        a = block_vars[i]
        b = block_vars[j]
        solver.add(a[POS] != b[POS])
        solver.add(a[NEG] != b[NEG])

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

            # blocks in a pair can only have before/after relationship
            for p in symm_pair:
                a = block_vars[p[0]]
                b = block_vars[p[1]]
                # [a, b]: a must be before or after b
                solver.add(z3.Or(
                    z3.And(a[POS] < b[POS], a[NEG] < b[NEG]),
                    z3.And(a[POS] > b[POS], a[NEG] > b[NEG])
                ))

            # self symmetric blocks can only have above/below relationship
            for p in itertools.combinations(symm_self, 2):
                a = block_vars[p[0]]
                b = block_vars[p[1]]
                # [a], [b]: a must be above or below b
                solver.add(z3.Or(
                    z3.And(a[POS] < b[POS], a[NEG] > b[NEG]),
                    z3.And(a[POS] > b[POS], a[NEG] < b[NEG])
                ))

            # self symmetric blocks cannot be before/after a pair of blocks
            for i in symm_self:
                s = block_vars[i]
                for j, k in symm_pair:
                    a = block_vars[j]
                    b = block_vars[k]
                    # [a,b], [s]: s cannot be before a and b
                    solver.add(z3.Not(z3.And(s[POS] < a[POS], s[POS] < b[POS], s[NEG] < a[NEG], s[NEG] < b[NEG])))
                    # [a,b], [s]: s cannot be after a and b
                    solver.add(z3.Not(z3.And(s[POS] > a[POS], s[POS] > b[POS], s[NEG] > a[NEG], s[NEG] > b[NEG])))

            # blocks in two separate pairs should not conflict
            for p in itertools.combinations(symm_pair, 2):
                a = block_vars[p[0][0]]
                b = block_vars[p[0][1]]
                c = block_vars[p[1][0]]
                d = block_vars[p[1][1]]
                # [a,b], [c,d]: a,b cannot be before c,d
                solver.add(z3.Not(z3.And(
                    a[POS] < c[POS], a[POS] < d[POS], b[POS] < c[POS], b[POS] < d[POS],
                    a[NEG] < c[NEG], a[NEG] < d[NEG], b[NEG] < c[NEG], b[NEG] < d[NEG],
                )))
                # [a,b], [c,d]: a,b cannot be after c,d
                solver.add(z3.Not(z3.And(
                    a[POS] > c[POS], a[POS] > d[POS], b[POS] > c[POS], b[POS] > d[POS],
                    a[NEG] > c[NEG], a[NEG] > d[NEG], b[NEG] > c[NEG], b[NEG] > d[NEG],
                )))
                # [a,b], [c,d]. a cannot be above c and below d
                solver.add(z3.Not(z3.And(
                    a[POS] < c[POS], a[POS] > d[POS],
                    a[NEG] > c[NEG], a[NEG] < d[NEG],
                )))
                # [a,b], [c,d]. a cannot be below c and above d
                solver.add(z3.Not(z3.And(
                    a[POS] > c[POS], a[POS] < d[POS],
                    a[NEG] < c[NEG], a[NEG] > d[NEG],
                )))
                # [a,b], [c,d]. b cannot be above c and below d
                solver.add(z3.Not(z3.And(
                    b[POS] < c[POS], b[POS] > d[POS],
                    b[NEG] > c[NEG], b[NEG] < d[NEG],
                )))
                # [a,b], [c,d]. b cannot be below c and above d
                solver.add(z3.Not(z3.And(
                    b[POS] > c[POS], b[POS] < d[POS],
                    b[NEG] < c[NEG], b[NEG] > d[NEG],
                )))

        elif const["constraint"] == "Order":
            for i, j in more_itertools.pairwise(const["instances"]):
                a = block_vars[i]
                b = block_vars[j]
                if const["direction"] == "top_to_bottom":
                    # a,b: a must be before b
                    solver.add(z3.And(a[POS] < b[POS], a[NEG] > b[NEG]))
                    if "abut" in const and const["abut"]:
                        # any block c cannot be below a and above b
                        for k in blocks:
                            if k not in [i, j]:
                                c = block_vars[k]
                                solver.add(z3.Not(z3.And(
                                    a[POS] < c[POS], c[POS] < b[POS],
                                    a[NEG] > c[NEG], c[NEG] > b[NEG])))
                elif const["direction"] == "left_to_right":
                    # a,b: a must be above b
                    solver.add(z3.And(a[POS] < b[POS], a[NEG] < b[NEG]))
                    if "abut" in const and const["abut"]:
                        # any block c cannot be after a and before b
                        for k in blocks:
                            if k not in [i, j]:
                                c = block_vars[k]
                                solver.add(z3.Not(z3.And(
                                    a[POS] < c[POS], c[POS] < b[POS],
                                    a[NEG] < c[NEG], c[NEG] < b[NEG])))
                else:
                    assert False

        elif const["constraint"] == "Align":
            for i, j in itertools.combinations(const["instances"], 2):
                a = block_vars[i]
                b = block_vars[j]
                if const["direction"] == "h_bottom":
                    # a cannot be above b
                    solver.add(z3.Not(z3.And(a[POS] < b[POS], a[NEG] > b[NEG])))
                    # a cannot be below b
                    solver.add(z3.Not(z3.And(a[POS] > b[POS], a[NEG] < b[NEG])))
                elif const["direction"] == "v_left":
                    # a cannot be before b
                    solver.add(z3.Not(z3.And(a[POS] < b[POS], a[NEG] < b[NEG])))
                    # a cannot be after b
                    solver.add(z3.Not(z3.And(a[POS] > b[POS], a[NEG] > b[NEG])))
                else:
                    assert False

    # print(solver)
    initial_pair = find_solution(solver)
    if n < 2 or not initial_pair:
        return(initial_pair)
    else:
        m = solver.model()
        previous_solution = {str(p): m[p].as_long() for p in m}
        sequence_pairs = [initial_pair]
        for i in range(n):

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


def test_merge_align_constraints():
    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "h_bottom",  "instances": ["b", "c"]}
    ]
    assert merge_align_constraints(constraints) == [{"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b", "c"]}]

    constraints = [
        {"constraint": "Align", "direction": "v_left", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "v_left", "instances": ["b", "c"]}
    ]
    assert merge_align_constraints(constraints) == [{"constraint": "Align", "direction": "v_left", "instances": ["a", "b", "c"]}]


def test_order():
    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["a", "c"], "abut": True},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["a", "b", "c"]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "a"], "abut": True},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())


def test_align():
    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "v_left",   "instances": ["b", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Align", "direction": "h_bottom", "instances": ["b", "c"]},
        {"constraint": "Align", "direction": "v_left",   "instances": ["a", "c"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b"]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["b", "a"]},
        ]
    assert not generate_sequence_pair(constraints, z3.Solver())


def test_symmetry():
    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["a", "b"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["c", "b", "a"]},
    ]
    assert not generate_sequence_pair(constraints, z3.Solver())

    constraints = [
        {"constraint": "SymmetricBlocks", "direction": "V", "pairs": [["a", "b"], ["c"]]},
        {"constraint": "Align", "direction": "v_left", "instances": ["b", "a"]},
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
    constraints = [
        {"constraint": "Align", "direction": "h_bottom", "instances": ["a", "b", "c"]},
    ]
    s = time.time()
    sequence_pairs = generate_sequence_pair(constraints, z3.Solver(), n=24)
    e = time.time()
    print(f"{len(sequence_pairs)} variants generated in {e-s:0.3f} seconds")
    for p in sequence_pairs:
        print(p)
    assert len(sequence_pairs) == 6
