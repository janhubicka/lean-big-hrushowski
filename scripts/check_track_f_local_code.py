"""Finite adversarial check of full adjacency code versus pointwise automorphisms.

Each test selects a complete source enumeration e and a target enumeration
f, forms the actual permutation h=e^{-1}f, and independently compares:
 (a) equality of matrices in enumeration coordinates against h being
     an automorphism;
 (b) equality at old positions against h fixing the old part pointwise.
This does not import the manuscript's checker or prove an infinite BRD.
"""
from itertools import combinations, permutations, product
import json


def run():
    n_orientations = n_bases = n_compared = n_fibres = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        enums = list(permutations(range(n)))
        baselines = enums if n < 4 else (enums[0], enums[len(enums) // 2], enums[-1])
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), c in zip(pairs, choices):
                if c == 1:
                    out[a] |= 1 << b
                elif c == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            n_orientations += 1
            for base in range(1 << n):
                if any(out[v] & ~base for v in range(n) if base >> v & 1):
                    continue
                n_bases += 1
                for e in baselines:
                    fiber_size = 0
                    for f in enums:
                        change = [0] * n
                        for i in range(n):
                            change[e[i]] = f[i]
                        same_code = all(
                            bool(out[e[i]] >> e[j] & 1) ==
                            bool(out[f[i]] >> f[j] & 1)
                            for i in range(n) for j in range(n)
                        )
                        automorphism = all(
                            bool(out[x] >> y & 1) ==
                            bool(out[change[x]] >> change[y] & 1)
                            for x in range(n) for y in range(n)
                        )
                        equal_old_positions = all(
                            f[i] == e[i] for i in range(n) if base >> e[i] & 1
                        )
                        fixes_old_pointwise = all(
                            change[x] == x for x in range(n) if base >> x & 1
                        )
                        assert same_code == automorphism
                        assert equal_old_positions == fixes_old_pointwise
                        if same_code and equal_old_positions:
                            fiber_size += 1
                        n_compared += 1
                    assert fiber_size >= 1
                    n_fibres += 1
    assert (n_orientations, n_bases, n_compared, n_fibres) == (
        653, 3577, 252115, 11093
    )
    fork = (0, 0, 0b011)
    swapped_sinks = (1, 0, 2)
    assert all(
        bool(fork[x] >> y & 1) ==
        bool(fork[swapped_sinks[x]] >> swapped_sinks[y] & 1)
        for x in range(3) for y in range(3)
    )
    assert any(swapped_sinks[x] != x for x in (0, 1))
    return {
        "status": "PASS",
        "orientations": n_orientations,
        "successor_closed_bases": n_bases,
        "enumeration_pairs": n_compared,
        "base_enumeration_fibres": n_fibres,
        "negative": "fork sink swap is setwise but not pointwise",
        "scope": "finite only",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
