#!/usr/bin/env python3
"""Independent finite adversarial checks for R0 A.3(2) and A.4 closure cores.

Enumerates all reflexive, transitive one-generated closure relations on
at most four vertices. Tests complete depth-prefix retention and all
closed stem-compatible subsets for the splicing construction, plus the
relative-A4 deletion core and its protected prefixes.

These are finite regressions, not proofs of any infinite tail-extension
or pigeonhole statement. The general lemmas are proved in the Lean
modules HrushovskiEllentuckSplicing and HrushovskiEllentuckThinning.
"""
from collections import Counter
from itertools import product


def audit(max_n: int = 4) -> Counter:
    counts = Counter()
    found_nonclosed_intermediate = False
    for n in range(max_n + 1):
        options = [
            [mask for mask in range(1 << n) if mask & (1 << i)]
            for i in range(n)
        ]
        for closure in product(*options):
            if any(
                closure[w] & ~closure[v]
                for v in range(n) for w in range(n)
                if closure[v] & (1 << w)
            ):
                continue
            counts["preorders"] += 1
            closed = [
                s for s in range(1 << n)
                if all(
                    not (closure[v] & ~s)
                    for v in range(n) if s & (1 << v)
                )
            ]
            closed_set = set(closed)
            for Y in closed:
                for X in closed:
                    if X & ~Y:
                        continue
                    for D in range(1 << n):
                        if D & ~Y:
                            continue
                        W = X
                        for v in range(n):
                            if Y & (1 << v) and closure[v] & D:
                                W |= 1 << v
                        V = sum(
                            1 << v for v in range(n)
                            if Y & (1 << v) and not (closure[v] & ~W)
                        )
                        counts["splice"] += 1
                        assert X & ~V == 0
                        assert V in closed_set
                        for C in closed:
                            if C & ~Y or C & ~(X | D):
                                continue
                            counts["protected_prefix"] += 1
                            assert C & ~V == 0
                        for Z in closed:
                            if Z & ~V or Z & D:
                                continue
                            counts["closed_stem"] += 1
                            assert Z & ~X == 0
                        found_nonclosed_intermediate |= W not in closed_set
                for U in range(1 << n):
                    Q = sum(
                        1 << v for v in range(n)
                        if Y & (1 << v) and not (closure[v] & U)
                    )
                    counts["thinning"] += 1
                    assert Q in closed_set
                    assert Q & U == 0
                    for C in closed:
                        if C & ~Y or C & U:
                            continue
                        counts["retained_prefix"] += 1
                        assert C & ~Q == 0
    assert found_nonclosed_intermediate, "Missing negative control: W need not be closed"
    return counts


if __name__ == "__main__":
    result = audit()
    expected = {
        "preorders": 390,
        "splice": 69490,
        "protected_prefix": 287213,
        "closed_stem": 118095,
        "thinning": 38501,
        "retained_prefix": 69490,
    }
    assert dict(result) == expected, (dict(result), expected)
    print("PASS: complete A.3/A.4 closure-core finite regressions", dict(result))
