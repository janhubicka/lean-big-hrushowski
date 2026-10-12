#!/usr/bin/env python3
"""Independent finite regression for half-open joins of nonempty block traces.

Pure arithmetic diagnostics: not a proof of the Lean or structural C0 theorems.
"""
from itertools import product

count = 0
positions = 0
inside = 0
boundaries = 0
for number in range(1, 7):
    for lengths in product(range(1, 5), repeat=number):
        cuts = [0]
        for l in lengths:
            cuts.append(cuts[-1] + l)
        stages = [(n, j) for n, l in enumerate(lengths) for j in range(l)]
        assert len(stages) == cuts[-1]
        for i, (n, j) in enumerate(stages):
            assert cuts[n] <= i < cuts[n + 1]
            assert j == i - cuts[n] and 0 <= j < lengths[n]
            matching = [k for k in range(number) if cuts[k] <= i < cuts[k+1]]
            assert matching == [n]
            if i + 1 == len(stages):
                continue
            successor = stages[i + 1]
            if j + 1 < lengths[n]:
                assert successor == (n, j + 1)
                inside += 1
            else:
                assert n + 1 < number
                assert successor == (n + 1, 0)
                assert i + 1 == cuts[n + 1]
                boundaries += 1
            assert i + 1 == cuts[successor[0]] + successor[1]
        count += 1
        positions += len(stages)
assert count == sum(4 ** k for k in range(1, 7))
print({"block_length_vectors": count, "positions": positions,
       "internal_successors": inside, "boundary_successors": boundaries})
