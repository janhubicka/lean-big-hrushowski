"""Independent finite check of extending old labels by fresh Nat labels.

Every injection of finite A into finite B is tested with arbitrary injective
Nat labels on A. The finite ordinal encoding of B is taken as the identity.
This is a regression test, not a general Lean proof.
"""
from itertools import permutations

checked = 0
old_values = range(9)
for na in range(5):
    for nb in range(na, 6):
        for image in permutations(range(nb), na):
            f = dict(enumerate(image))
            inv = {b: a for a, b in f.items()}
            for original in permutations(old_values, na):
                e = dict(enumerate(original))
                sup = max(original, default=0)
                new = {
                    b: e[inv[b]] if b in inv else sup + 1 + b
                    for b in range(nb)
                }
                assert len(set(new.values())) == nb
                for a in range(na):
                    assert new[f[a]] == e[a]
                for b in range(nb):
                    if b not in inv:
                        assert new[b] > sup
                        assert all(new[b] != v for v in e.values())
                checked += 1

assert checked > 10000
print(f"Checked {checked} injections and arbitrary old Nat labellings.")
