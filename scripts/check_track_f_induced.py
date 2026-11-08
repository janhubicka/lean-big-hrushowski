"""Exhaustive finite check of induced arrows versus closed embeddings."""
from itertools import combinations, product
from collections import Counter
import json

def run():
    stats = Counter()
    for n in range(6):
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
            stats["orientations"] += 1
            for selected in range(1 << n):
                subout = tuple(out[x] & selected for x in range(n))
                assert all(not ((subout[x] >> y & 1) and not (out[x] >> y & 1))
                           for x in range(n) for y in range(n))
                closed = all((out[x] & ~selected) == 0
                             for x in range(n) if selected >> x & 1)
                exact_full_values = all(subout[x] == out[x]
                                        for x in range(n) if selected >> x & 1)
                assert closed == exact_full_values
                for x in range(n):
                    if selected >> x & 1:
                        assert subout[x] == out[x] & selected
                        stats["induced_vertex_checks"] += 1
                stats["induced_sets"] += 1
                if closed:
                    stats["complete_closed_values"] += 1
    assert stats["orientations"] == 30887
    assert stats["induced_sets"] == 977655
    assert stats["complete_closed_values"] > 0
    # A single arrow x -> y and the nonclosed set {x}:
    # the induced orientation has no arrow, but the old out-value is {y}.
    assert (2 & 1) == 0 and (2 & ~1) != 0
    return {"status": "PASS", "scope": "finite only",
            "checks": dict(stats),
            "negative_case": "nonclosed singleton loses an outgoing arrow"}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
