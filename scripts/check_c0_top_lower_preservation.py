#!/usr/bin/env python3
"""Adversarial finite check: top relabelling preserves exact lower C/graph matrices.

Enumerates arbitrary complete matrices (a stronger test class than C0 admissibility),
then checks the selected least representative, all allowed permutations, and a
counterexample to weakening pointwise fixing of the ordered lower part to setwise fixing.
"""
from itertools import permutations
from random import Random


def pairs_of_mask(n, mask):
    return frozenset((i, j) for i in range(n) for j in range(n)
                     if mask & (1 << (i * n + j)))


def relabel(pairs, perm):
    return frozenset((perm[i], perm[j]) for i, j in pairs)


def lower_code(adj, closure, lower):
    return (frozenset((i, j) for i, j in adj if i in lower and j in lower),
            frozenset((i, j) for i, j in closure if i in lower and j in lower))


def lower_c_closed(closure, lower):
    return all(v in lower for (u, v) in closure if u in lower)


def unchanged_lower_rows(old_c, new_c, lower, n):
    return all(((u, v) in old_c) == ((u, v) in new_c)
               for u in lower for v in range(n))


def code_key(adj, closure, lower):
    return (tuple(sorted(adj)), tuple(sorted(closure)), tuple(sorted(lower)))


def test(n, adj, closure, lower):
    old = lower_code(adj, closure, lower)
    allowed = [p for p in permutations(range(n)) if all(p[u] == u for u in lower)]
    closed = lower_c_closed(closure, lower)
    assert allowed
    all_codes = []
    for p in allowed:
        new_adj, new_closure = relabel(adj, p), relabel(closure, p)
        new_lower = frozenset(p[u] for u in lower)
        assert new_lower == lower
        assert lower_code(new_adj, new_closure, new_lower) == old
        if closed:
            assert unchanged_lower_rows(closure, new_closure, lower, n)
        all_codes.append((new_adj, new_closure, new_lower))
    least = min(all_codes, key=lambda c: code_key(*c))
    assert lower_code(*least) == old
    if closed:
        assert unchanged_lower_rows(closure, least[1], lower, n)
    return len(allowed)


def main():
    trials = 0
    verified_perms = 0
    for n in range(3):
        m = n * n
        for amask in range(1 << m):
            adj = pairs_of_mask(n, amask)
            for cmask in range(1 << m):
                closure = pairs_of_mask(n, cmask)
                for lmask in range(1 << n):
                    lower = frozenset(i for i in range(n) if lmask & (1 << i))
                    verified_perms += test(n, adj, closure, lower)
                    trials += 1
    rng = Random(20261111)
    for n, count in [(3, 12000), (4, 12000)]:
        for _ in range(count):
            adj = pairs_of_mask(n, rng.getrandbits(n * n))
            closure = pairs_of_mask(n, rng.getrandbits(n * n))
            lower = frozenset(i for i in range(n) if rng.getrandbits(1))
            verified_perms += test(n, adj, closure, lower)
            trials += 1

    # Concrete C-closed, reflexive, nested lower part; swapping the
    # *ordered* lower vertices only setwise changes the full C-matrix.
    lower = frozenset({0, 1})
    closure = frozenset({(0, 0), (0, 1), (1, 1),
                         (2, 0), (2, 1), (2, 2)})
    swap = (1, 0, 2)
    assert frozenset(swap[i] for i in lower) == lower
    assert any(swap[i] != i for i in lower)
    assert lower_code(frozenset(), closure, lower) != lower_code(
        frozenset(), relabel(closure, swap), lower)
    # Without lower C-closedness a top permutation can change a full
    # C-row from a lower vertex while fixing its induced lower submatrix.
    nonclosed = frozenset({(0, 0), (0, 1), (1, 1), (2, 2)})
    top_swap = (0, 2, 1)
    assert not lower_c_closed(nonclosed, frozenset({0}))
    assert lower_code(frozenset(), nonclosed, frozenset({0})) == lower_code(
        frozenset(), relabel(nonclosed, top_swap), frozenset({0}))
    assert not unchanged_lower_rows(nonclosed, relabel(nonclosed, top_swap),
                                    frozenset({0}), 3)
    print(f"OK: {trials:,} complete matrices; {verified_perms:,} top-fixed permutations; "
          "min-normal-form and closed-row checks; both negative controls")


if __name__ == "__main__":
    main()
