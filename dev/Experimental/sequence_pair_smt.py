import z3
import time
import itertools

block_vars = dict()
pos = 'pos'
neg = 'neg'

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


def define_vars(block_vars, b):
    if b not in block_vars:
        block_vars[b] = dict()
        block_vars[b][pos] = z3.Int(f"pos_{b}")
        block_vars[b][neg] = z3.Int(f"neg_{b}")


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

num_blocks = len(block_vars)
# print(block_vars)
print(f"{num_blocks=}")

solver = z3.Solver()

# Restrict range of each variable
for b, d in block_vars.items():
    solver.add(z3.And(d[pos] > 0, d[pos] <= num_blocks))
    solver.add(z3.And(d[neg] > 0, d[neg] <= num_blocks))

# Two blocks cannot occupy the same index
blocks = [b for b in block_vars.keys()]

for i, j in itertools.combinations(blocks, 2):
    a = block_vars[i]
    b = block_vars[j]
    solver.add(a[pos] != b[pos])
    solver.add(a[neg] != b[neg])

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
                z3.And(a[pos] < b[pos], a[neg] < b[neg]),
                z3.And(a[pos] > b[pos], a[neg] > b[neg])
            ))

        # self symmetric blocks can only have above/below relationship
        for p in itertools.combinations(symm_self, 2):
            a = block_vars[p[0]]
            b = block_vars[p[1]]
            # [a], [b]: a must be above or below b
            solver.add(z3.Or(
                z3.And(a[pos] < b[pos], a[neg] > b[neg]),
                z3.And(a[pos] > b[pos], a[neg] < b[neg])
            ))

        # self symmetric blocks cannot be before/after a pair of blocks
        for i in symm_self:
            s = block_vars[i]
            for j, k in symm_pair:
                a = block_vars[j]
                b = block_vars[k]
                # [a,b], [s]: s cannot be before a and b
                solver.add(z3.Not(z3.And(s[pos] < a[pos], s[pos] < b[pos], s[neg] < a[neg], s[neg] < b[neg])))
                # [a,b], [s]: s cannot be after a and b
                solver.add(z3.Not(z3.And(s[pos] > a[pos], s[pos] > b[pos], s[neg] > a[neg], s[neg] > b[neg])))

        for p in itertools.combinations(symm_pair, 2):
            a = block_vars[p[0][0]]
            b = block_vars[p[0][1]]
            c = block_vars[p[1][0]]
            d = block_vars[p[1][1]]
            # [a,b], [c,d]: a,b cannot be before c,d
            solver.add(z3.Not(z3.And(
                a[pos] < c[pos], a[pos] < d[pos], b[pos] < c[pos], b[pos] < d[pos],
                a[neg] < c[neg], a[neg] < d[neg], b[neg] < c[neg], b[neg] < d[neg],
            )))
            # [a,b], [c,d]: a,b cannot be after c,d
            solver.add(z3.Not(z3.And(
                a[pos] > c[pos], a[pos] > d[pos], b[pos] > c[pos], b[pos] > d[pos],
                a[neg] > c[neg], a[neg] > d[neg], b[neg] > c[neg], b[neg] > d[neg],
            )))
            # [a,b], [c,d]. a cannot be above c and below d
            solver.add(z3.Not(z3.And(
                a[pos] < c[pos], a[pos] > d[pos],
                a[neg] > c[neg], a[neg] < d[neg],
            )))
            # [a,b], [c,d]. a cannot be below c and above d
            solver.add(z3.Not(z3.And(
                a[pos] > c[pos], a[pos] < d[pos],
                a[neg] < c[neg], a[neg] > d[neg],
            )))
            # [a,b], [c,d]. b cannot be above c and below d
            solver.add(z3.Not(z3.And(
                b[pos] < c[pos], b[pos] > d[pos],
                b[neg] > c[neg], b[neg] < d[neg],
            )))
            # [a,b], [c,d]. b cannot be below c and above d
            solver.add(z3.Not(z3.And(
                b[pos] > c[pos], b[pos] < d[pos],
                b[neg] < c[neg], b[neg] > d[neg],
            )))

    elif const["constraint"] == "Order":
        for i, j in itertools.combinations(const["instances"], 2):
            a = block_vars[i]
            b = block_vars[j]
            if const["direction"] == "top_to_bottom":
                # a,b: a must be before b
                solver.add(z3.And(a[pos] < b[pos], a[neg] > b[neg]))
                if getattr(const, "abut", False):
                    # any block c cannot be below a and above b
                    for k in blocks:
                        if k not in [i, j]:
                            c = block_vars[k]
                            solver.add(z3.Not(z3.And(
                                a[pos] < c[pos], c[pos] < b[pos],
                                a[neg] > c[neg], c[neg] > b[neg])))
            else:
                # a,b: a must be above b
                solver.add(z3.And(a[pos] < b[pos], a[neg] < b[neg]))
                if getattr(const, "abut", False):
                    # any block c cannot be after a and before b
                    for k in blocks:
                        if k not in [i, j]:
                            c = block_vars[k]
                            solver.add(z3.Not(z3.And(
                                a[pos] < c[pos], c[pos] < b[pos],
                                a[neg] < c[neg], c[neg] < b[neg])))

    elif const["constraint"] == "Align":
        for i, j in itertools.combinations(const["instances"], 2):
            a = block_vars[i]
            b = block_vars[j]
            if const["direction"] == "h_bottom":
                # a can only be before or after b
                solver.add(z3.Or(
                    z3.And(a[pos] < b[pos], a[neg] < b[neg]),
                    z3.And(a[pos] > b[pos], a[neg] > b[neg])
                ))
            elif const["direction"] == "v_left":
                # a can only be above or below b
                solver.add(z3.Or(
                    z3.And(a[pos] < b[pos], a[neg] > b[neg]),
                    z3.And(a[pos] > b[pos], a[neg] < b[neg])
                ))

# Solve
s = time.time()
r = solver.check()
e = time.time()
print(f"Elapsed time: {e-s:0.3f} seconds")
# print(r, solver.model())
if r == z3.sat:
    m = solver.model()

    seq_pos = [(b, m[b]) for b in m if str(b).startswith("pos")]
    seq_neg = [(b, m[b]) for b in m if str(b).startswith("neg")]

    seq_pos = sorted(seq_pos, key=lambda x: x[1].as_long())
    seq_neg = sorted(seq_neg, key=lambda x: x[1].as_long())

    seq_pos = [str(b[0]).split("_")[1] for b in seq_pos]
    seq_neg = [str(b[0]).split("_")[1] for b in seq_neg]

    seq_pos = "".join(seq_pos)
    seq_neg = "".join(seq_neg)

    # print(sorted([(d, m[d]) for d in m], key=lambda x: str(x[0])))

    print(f"Sequence pair: {seq_pos}, {seq_neg}")
else:
    assert False, "Legal sequence pair not found"
