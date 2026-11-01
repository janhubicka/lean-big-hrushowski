"""Finite adversarial check of complete code versus pointwise automorphisms.

This is independent of the published manuscript's orientation checker.
It checks the exact change-of-enumeration condition, not BRD.
"""
from itertools import combinations, permutations, product
import json


def run():
    orientations = closed_bases = comparisons = orbit_sum = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), c in zip(pairs, choices):
                if c == 1:
                    out[a] |= 1 << b
                elif c == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            orientations += 1
            for base in range(1 << n):
                if any(out[i] & ~base for i in range(n) if base >> i & 1):
                    continue
                closed_bases += 1
                local_count = 0
                for perm in permutations(range(n)):
                    same_code = all(bool(out[x] >> y & 1) ==
                                    bool(out[perm[x]] >> perm[y] & 1)
                                    for x in range(n) for y in range(n))
                    same_lower = all(perm[x] == x for x in range(n)
                                     if base >> x & 1)
                    pointwise_aut = (same_code and same_lower)
                    assert (same_code and same_lower) == pointwise_aut
                    local_count += pointwise_aut
                    comparisons += 1
                assert local_count >= 1
                orbit_sum += local_count
    assert (orientations, closed_bases, comparisons, orbit_sum) == (
        653, 3577, 83291, 4058)
    fork = (0, 0, 0b011)
    swapped_sinks = (1, 0, 2)
    assert all(bool(fork[x] >> y & 1) ==
               bool(fork[swapped_sinks[x]] >> swapped_sinks[y] & 1)
               for x in range(3) for y in range(3))
    assert not all(swapped_sinks[x] == x for x in (0, 1))
    return {"status": "PASS", "orientations": orientations,
            "successor_closed_bases": closed_bases,
            "enumerations_compared": comparisons,
            "sum_local_stabilizer_sizes": orbit_sum,
            "negative": "sink swap fixes lower part setwise but not pointwise",
            "scope": "finite only"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
