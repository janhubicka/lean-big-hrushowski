"""Independent check of all fixed-lower minimum complete-matrix fibres.

All oriented graphs of outdegree <= 2 through four vertices, every
old subset, and two representative base enumerations; sampled five
vertex cases.  Independent of Lean and all manuscript counting code.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json


def all_orientations(n):
    pairs = tuple(combinations(range(n), 2))
    for choices in product(range(3), repeat=len(pairs)):
        out = [0] * n
        for (x, y), k in zip(pairs, choices):
            if k == 1:
                out[x] |= 1 << y
            elif k == 2:
                out[y] |= 1 << x
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)


def code(out, enum):
    return tuple(int(bool(out[x] & (1 << y)))
                 for x in enum for y in enum)


def pointwise_group_order(out, P, perms):
    return sum(
        all(p[x] == x for x in P)
        and all(bool(out[x] & (1 << y)) ==
                bool(out[p[x]] & (1 << p[y]))
                for x in range(len(out)) for y in range(len(out)))
        for p in perms)


def check(out, base, oldmask, perms, tally):
    n = len(out)
    P = {i for i in range(n) if (oldmask >> i) & 1}
    fixed_positions = [i for i, x in enumerate(base) if x in P]
    fixed = [p for p in perms
             if all(p[i] == base[i] for i in fixed_positions)]
    assert fixed
    values = [code(out, p) for p in fixed]
    minimum = min(values)
    fibre = sum(k == minimum for k in values)
    stabilizer = pointwise_group_order(out, P, perms)
    assert fibre == stabilizer, (out, base, P, fibre, stabilizer)
    for f in fixed:
        for i, x in enumerate(f):
            if x in P:
                assert base[i] == x
    tally["cases"] += 1
    tally["minimum_fibre_elements"] += fibre


def main():
    tally = Counter()
    for n in range(5):
        perms = list(permutations(range(n)))
        for out in all_orientations(n):
            tally["orientations"] += 1
            for oldmask in range(1 << n):
                bases = [perms[0]]
                if perms[-1] != perms[0]:
                    bases.append(perms[-1])
                for base in bases:
                    check(out, base, oldmask, perms, tally)
    # A deterministic sample of genuinely five-vertex orientations.
    perms = list(permutations(range(5)))
    for ix, out in enumerate(all_orientations(5)):
        if ix % 137 == 0:
            tally["sampled_five_vertex_orientations"] += 1
            for oldmask in (0, 1, 3, 7, 15, 31):
                for base in (perms[0], perms[-1]):
                    check(out, base, oldmask, perms, tally)

    # Adversarial counterchecks to three dropped hypotheses.
    empty = (0, 0)
    two = [(0, 1), (1, 0)]
    assert pointwise_group_order(empty, set(), two) == 2
    assert len([two[0]]) == 1  # failure without orbit saturation
    assert pointwise_group_order(empty, {0}, two) == 1
    assert len(two) == 2  # setwise P, not pointwise old positions
    one_edge = (2, 0)
    assert pointwise_group_order(one_edge, set(), two) == 1
    assert len(two) == 2  # constant/incomplete code merges two orbits
    print(json.dumps(dict(tally), sort_keys=True))


if __name__ == "__main__":
    main()
