"""Hostile finite regression for literal row-major codes versus local types.

The manuscript fixes an arbitrary *ordered representative* for each
unordered local closure with ordered lower part. Lex minimization is
an optional concrete representative convention, not the unique one.

Exhaust every two-orientation on up to four labelled vertices,
compare nested-row and flattened row-major codes, count complete-code
orbits for each old part, and exhibit the two admissible directed
3-cycle local types (three labelled orders each).
"""
from itertools import combinations, permutations, product
from collections import Counter
import json


def orientations(n):
    edges = list(combinations(range(n), 2))
    for assignment in product(range(3), repeat=len(edges)):
        out = [0] * n
        for (a, b), direction in zip(edges, assignment):
            if direction == 1:
                out[a] |= 1 << b
            elif direction == 2:
                out[b] |= 1 << a
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)


def matrix(out, order):
    return tuple(tuple(int(bool(out[a] & (1 << b))) for b in order)
                 for a in order)


def code(out, order):
    return tuple(v for row in matrix(out, order) for v in row)


def equal_code(out, e, f):
    return matrix(out, e) == matrix(out, f)


def same_oriented_graph(out, e, f):
    n = len(out)
    return all(bool(out[e[i]] & (1 << e[j])) ==
               bool(out[f[i]] & (1 << f[j]))
               for i in range(n) for j in range(n))


def run():
    totals = Counter()
    for n in range(5):
        for out in orientations(n):
            perms = tuple(permutations(range(n)))
            codes = {e:code(out, e) for e in perms}
            for e, f in product(perms, repeat=2):
                assert equal_code(out, e, f) == same_oriented_graph(out, e, f)
                assert (codes[e] == codes[f]) == equal_code(out, e, f)
                totals["pair_checks"] += 1
            assert sorted(codes.values()) == sorted(tuple(
                v for row in matrix(out, e) for v in row) for e in perms)
            totals["orientations"] += 1

    # A genuine counterexample to treating lex choice as printed:
    # the 3-cycle admits *two* different ordered local isomorphism
    # types with P=empty. Each type has an orbit of three labels.
    directed_cycle = (1 << 1, 1 << 2, 1 << 0)
    perms = tuple(permutations(range(3)))
    classes = {}
    for p in perms:
        classes.setdefault(code(directed_cycle, p), set()).add(p)
    assert len(classes) == 2
    assert sorted(map(len, classes.values())) == [3, 3]
    chosen_minimum = min(classes)
    assert len(classes[chosen_minimum]) == 3
    assert len([k for k in classes if k != chosen_minimum]) == 1
    totals["three_cycle_local_types"] = len(classes)
    totals["three_cycle_fibre_size"] = len(classes[chosen_minimum])
    print(json.dumps(dict(totals),sort_keys=True))


if __name__ == "__main__":
    run()
