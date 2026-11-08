#!/usr/bin/env python3
"""Independent finite regression for exact joined C0 component-index stages.

Checks *arbitrary* finite index assignments, including unused ranks,
a missing common base, and independent orders on the base. The
predimension and full unary values are audited separately in
check_c0_explicit_amalgam.py. These checks are not a proof certificate.
"""
from itertools import product

checks = cases = 0
shapes = [(p, l, r) for p in range(4) for l in range(4)
          for r in range(4) if p+l+r <= 5]
for p, l, r in shapes:
    for n in range(1, 5):
        for m in range(1, 5):
            for left in product(range(n), repeat=p+l):
                for right in product(range(m), repeat=p+r):
                    cases += 1
                    size = p+l+r
                    def joined(x):
                        if x < p+l:
                            return left[x]
                        return n+right[p+x-(p+l)]
                    for k in range(n+1):
                        expected = {x for x in range(p+l) if left[x] < k}
                        actual = {x for x in range(size) if joined(x) < k}
                        assert actual == expected
                        checks += 1
                    assert {x for x in range(size) if joined(x) < n} == set(range(p+l))
                    checks += 1
                    for j in range(m+2):
                        right_old = {x for x in range(p) if right[x] < j}
                        right_old |= {p+l+t for t in range(r) if right[p+t] < j}
                        expected = set(range(p+l)) | right_old
                        actual = {x for x in range(size) if joined(x) < n+j}
                        assert actual == expected
                        checks += 1

print({"shapes": len(shapes), "index_assignments": cases,
       "stage_equalities": checks, "failures": 0,
       "empty_base_and_unused_ranks_tested": True})
