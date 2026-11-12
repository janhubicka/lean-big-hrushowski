#!/usr/bin/env python3
"""Independent finite adversarial regression for the normalized top restriction lemma.

Tests arbitrary complete graph matrices together with complete C-matrices whose
lower rows stay inside the ordered lower part and whose top rows are full.
This is a *stronger test domain* than the admissible sparse C0 local types.
It does not substitute for a Lean proof or for recursive catalogue existence.
"""
from itertools import permutations
from random import Random


def relabel(pairs, sigma):
    return frozenset((sigma[u], sigma[v]) for u, v in pairs)


def support(c, a, n):
    return frozenset(v for v in range(n) if (a, v) in c)


def matrix_key(m):
    adj, c, lower = m
    return tuple(sorted(adj)), tuple(sorted(c)), tuple(sorted(lower))


def orbit(m, n):
    a, c, lower = m
    return frozenset((relabel(a, p), relabel(c, p), lower)
                     for p in permutations(range(n))
                     if all(p[u] == u for u in lower))


def check(m, n):
    a, c, lower = m
    all_indices = frozenset(range(n))
    assert all((u, v) not in c or v in lower
               for u in lower for v in range(n))
    assert all((u, v) in c for u in all_indices - lower for v in range(n))
    o = orbit(m, n)
    assert o
    normal = min(o, key=matrix_key)
    na, nc, nl = normal
    assert nl == lower
    assert orbit(normal, n) == o
    assert min(orbit(normal, n), key=matrix_key) == normal
    for x in range(n):
        if x in lower:
            before, after = support(c, x, n), support(nc, x, n)
            assert before == after
            assert before <= lower
            assert all(((u, v) in a) == ((u, v) in na)
                       and ((u, v) in c) == ((u, v) in nc)
                       for u in before for v in before)
            assert all(((x, v) in c) == ((x, v) in nc) for v in range(n))
        else:
            assert support(nc, x, n) == all_indices
    return len(o)


def main():
    rng = Random(20261112)
    checked = 0
    orbit_members = 0
    for n, runs in [(1, 40), (2, 400), (3, 4000), (4, 9000), (5, 1200)]:
        for _ in range(runs):
            lower = frozenset(i for i in range(n) if rng.getrandbits(1))
            a = frozenset((u, v) for u in range(n) for v in range(n)
                          if rng.getrandbits(1))
            c = frozenset((u, v) for u in range(n) for v in range(n)
                          if u not in lower or
                          (v in lower and (u == v or rng.getrandbits(1))))
            orbit_members += check((a, c, lower), n)
            checked += 1
    # Explicit negative control: without lower C-closedness the
    # generated closure of a lower vertex changes under top permutation.
    n, lower = 3, frozenset({0})
    c = frozenset({(0, 0), (0, 1), *[(u, v) for u in (1, 2) for v in range(n)]})
    sigma = (0, 2, 1)
    assert all(sigma[i] == i for i in lower)
    assert support(c, 0, n) != support(relabel(c, sigma), 0, n)
    print(f"OK: {checked:,} complete matrices, {orbit_members:,} distinct "
          "permuted orbit members, exact lower generated-code and top "
          "generation checks, idempotence, nonclosed negative control")


if __name__ == "__main__":
    main()
