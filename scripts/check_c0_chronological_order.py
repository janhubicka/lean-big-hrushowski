#!/usr/bin/env python3
"""Track D: adversarial finite checks of chronological component orders.

An order respecting distinct component indices induces consecutive
component intervals, and restricting that order to any finite vertex
subset retains the property. This is intentionally weaker than the
manuscript's fixed canonical internal order for each component type.
"""
from itertools import permutations, product


def main():
    valid = restrictions = interval_witnesses = 0
    for n in range(1, 5):
        for m in range(1, n + 1):
            for kappa in product(range(m), repeat=n):
                if set(kappa) != set(range(m)):
                    continue
                for order in permutations(range(n)):
                    rank = {v: i for i, v in enumerate(order)}
                    chronological = all(
                        rank[x] < rank[y]
                        for x in range(n) for y in range(n)
                        if kappa[x] < kappa[y]
                    )
                    if not chronological:
                        continue
                    valid += 1
                    for x, y, z in product(range(n), repeat=3):
                        if (kappa[x] == kappa[y]
                                and rank[x] < rank[z] < rank[y]):
                            assert kappa[z] == kappa[x]
                            interval_witnesses += 1
                    for mask in range(1 << n):
                        subset = {i for i in range(n) if mask & (1 << i)}
                        assert all(
                            rank[x] < rank[y]
                            for x in subset for y in subset
                            if kappa[x] < kappa[y]
                        )
                        restrictions += 1

    assert (valid, restrictions, interval_witnesses) == (221, 3282, 150)

    # A bad chronological order: the later component precedes the earlier one.
    kappa, order = (1, 0), (0, 1)
    pos = {v: i for i, v in enumerate(order)}
    assert kappa[1] < kappa[0] and pos[1] > pos[0]

    # Chronology alone does NOT select the internal order of one component:
    # both orders satisfy it for this two-vertex single-component example.
    kappa = (0, 0)
    for order in [(0, 1), (1, 0)]:
        pos = {v: i for i, v in enumerate(order)}
        assert all(pos[x] < pos[y] for x, y in product(range(2), repeat=2)
                   if kappa[x] < kappa[y])

    print(f"PASS: {valid} chronological finite presentations, "
          f"{restrictions} hereditary restrictions, "
          f"{interval_witnesses} component-convexity cases, "
          "and two negative controls")


if __name__ == "__main__":
    main()
