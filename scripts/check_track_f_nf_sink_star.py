"""Independent audit of the literal N_F sink-graph star extension.

For each two-orientation on up to four vertices and each selection
U of old sinks, add a new sink z and a predecessor x_a pointing to
a and z for each a in U. Check exact old induced edges, no loops,
no reverse arrows, outdegree <= 2, successor-closed old carrier,
the concrete predimension identity for every subset W, and the
strict old-base relative predimension inequality on every W meeting
the new domain. The last is a finite diagnostic, not a Lean theorem.
"""
from itertools import combinations, product
from collections import Counter
import json


def orientations(n):
    pairs = tuple(combinations(range(n), 2))
    for choices in product(range(3), repeat=len(pairs)):
        out = [0] * n
        for (a, b), k in zip(pairs, choices):
            if k == 1:
                out[a] |= 1 << b
            elif k == 2:
                out[b] |= 1 << a
        if all(x.bit_count() <= 2 for x in out):
            yield tuple(out)


def delta(out, subset):
    return 2 * len(subset) - sum(
        j in subset for i in subset for j in range(len(out))
        if out[i] & (1 << j))


def check(out, U, counts):
    n = len(out)
    m = len(U)
    z = n
    star = [0] * (n + 1 + m)
    for i in range(n):
        star[i] = out[i]
    for j, a in enumerate(U):
        star[n + 1 + j] = (1 << a) | (1 << z)
    assert star[z] == 0
    assert star[:n] == list(out)
    assert all(mask.bit_count() <= 2 for mask in star)
    assert all(not (mask & (1 << i)) for i, mask in enumerate(star))
    assert all(not (star[j] & (1 << i))
               for i, mask in enumerate(star) for j in range(len(star))
               if mask & (1 << j))
    for k in range(1 << len(star)):
        W = {i for i in range(len(star)) if (k >> i) & 1}
        D = W & set(range(n))
        t = sum(n + 1 + j in W for j in range(m))
        s = sum(n + 1 + j in W and a in D for j, a in enumerate(U))
        eps = int(z in W)
        actual = delta(star, W)
        claimed = delta(out, D) + 2 * eps + 2 * t - eps * t - s
        assert actual == claimed, (out, U, W, actual, claimed)
        counts["predim_identities"] += 1
        if W - set(range(n)):
            assert actual > delta(out, D), (out, U, W)
            counts["strict_relative_checks"] += 1
    counts["extensions"] += 1


def main():
    counts = Counter()
    for n in range(5):
        for out in orientations(n):
            counts["orientations"] += 1
            sinks = [x for x in range(n) if out[x] == 0]
            for mask in range(1 << len(sinks)):
                U = tuple(x for j, x in enumerate(sinks)
                          if (mask >> j) & 1)
                check(out, U, counts)
    # Why strictness cannot be inferred from simple successor-
    # closedness: in a fork, a sink pair is closed under arrows
    # but has the same predimension as its common predecessor.
    fork = (0, 0, (1 << 0) | (1 << 1))
    assert delta(fork, {0, 1}) == delta(fork, {0, 1, 2}) == 4
    print(json.dumps(dict(counts), sort_keys=True))


if __name__ == "__main__":
    main()
