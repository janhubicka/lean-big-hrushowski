"""Independent finite adversarial regression for strict strong-closure predimension.

Exhaustive labelled graphs on <=5 vertices. Predimension δ(X)=2|X|-|E(X)|,
self-sufficiency on finite subsets, and exact closure as intersection of
all globally strong finite supersets.
"""
from itertools import combinations

checks = {"graphs": 0, "two_sparse_graphs": 0, "closures": 0,
          "strict": 0, "same_predimension": 0, "same_pattern": 0}

for n in range(6):
    edges = list(combinations(range(n), 2))
    full = (1 << n) - 1
    edge_masks = [(1 << a) | (1 << b) for a, b in edges]
    for e in range(1 << len(edges)):
        checks["graphs"] += 1
        selected = [em for k, em in enumerate(edge_masks) if e & (1 << k)]
        delta = [2 * v.bit_count() - sum((em & v) == em for em in selected)
                 for v in range(full + 1)]
        if any(d < 0 for d in delta):
            continue
        checks["two_sparse_graphs"] += 1
        strong = [a for a in range(full + 1)
                  if all(delta[a] <= delta[b] for b in range(full + 1)
                         if (a & b) == a)]
        for x in range(full + 1):
            c = full
            for y in strong:
                if (x & y) == x:
                    c &= y
            assert c in strong and (x & c) == x
            checks["closures"] += 1
            for d in range(full + 1):
                if (x & d) == x and (c & d) == d and d != c:
                    checks["strict"] += 1
                    assert delta[c] < delta[d], (n, e, x, c, d)
            for b in range(full + 1):
                if (x & b) == x and delta[b] == delta[c]:
                    checks["same_predimension"] += 1
                    assert (c & b) == c, (n, e, x, c, b)
                    if b.bit_count() == c.bit_count():
                        checks["same_pattern"] += 1
                        assert b == c, (n, e, x, c, b)

# Negative control: minimality is essential even for a strong container.
# Two edgeless vertices: C={0,1} is strong, X=D={0}, and δ(D)<δ(C).
x, d, c = 0b01, 0b01, 0b11
assert 2 * d.bit_count() < 2 * c.bit_count()
print(checks)
print("Non-minimal strong-container counterexample passed.")
