"""Adversarial tests for prefix-dependent uniform finite choice counts.
This checks actual sets of histories, not a simplified independent product.
"""
from itertools import product
from math import prod

def histories(n, prefix, choose):
    if n == 0:
        return {()}
    return {(a,) + rest for a in choose(n-1, prefix)
            for rest in histories(n-1, (a,) + prefix, choose)}

def run():
    totals = {}
    for depth in range(7):
        for seed in product(range(3), repeat=2):
            g = lambda n: (n + seed[0]) % 4
            def choice(n, prefix):
                k = g(n)
                shift = (sum(prefix) * 5 + len(prefix) + n + seed[1]) % 11
                return {(shift + j) % 17 for j in range(k)}
            observed = histories(depth, (), choice)
            assert all(len(x) == depth for x in observed)
            assert len(observed) == prod(g(n) for n in range(depth))
            totals[(depth, seed)] = len(observed)
    # Nonuniform branch size is essential; with two first choices
    # and second branch sizes 1 and 2, there are three histories.
    def varying(n, prefix):
        if n == 1:
            return {0, 1}
        return {0} if prefix == (0,) else {0, 1}
    assert len(histories(2, (), varying)) == 3
    assert len(histories(2, (), varying)) != 2
    return dict(status="PASS", uniform_instances=len(totals),
                negative="branch sizes depend on the prefix")

if __name__ == "__main__":
    import json
    print(json.dumps(run(), indent=2))
