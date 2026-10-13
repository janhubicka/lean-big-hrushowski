#!/usr/bin/env python3
"""Exhaustive finite adversarial check of tagged dependency closure.

The base is a common set of component indices, the tails are disjoint.
Dependency relations may contain cycles and loops, so this checks a
stronger path-closure lemma than the acyclic Hrushovski application.
"""


def reach(adj, root):
    ans, queue = {root}, [root]
    for x in queue:
        for y in adj[x]:
            if y not in ans:
                ans.add(y)
                queue.append(y)
    return ans


def edge_rows(n, mask):
    return [{v for v in range(n) if (mask >> (u * n + v)) & 1}
            for u in range(n)]


def base_closed(rows, p):
    return all(all(y < p for y in rows[x]) for x in range(p))


def agree_on_base(lrows, rrows, p):
    return all((v in lrows[u]) == (v in rrows[u])
               for u in range(p) for v in range(p))


def validate(p, l, r):
    nl, nr, nt = p + l, p + r, p + l + r
    lmap = tuple(range(nl))
    rmap = tuple(range(p)) + tuple(range(p + l, nt))
    left_cases = [edge_rows(nl, m) for m in range(1 << (nl * nl))]
    right_cases = [edge_rows(nr, m) for m in range(1 << (nr * nr))]
    left_cases = [x for x in left_cases if base_closed(x, p)]
    right_cases = [x for x in right_cases if base_closed(x, p)]
    cases = paths = 0
    for dl in left_cases:
        for dr in right_cases:
            if not agree_on_base(dl, dr, p):
                continue
            joint = [set() for _ in range(nt)]
            for u in range(nl):
                joint[lmap[u]].update(lmap[v] for v in dl[u])
            for u in range(nr):
                joint[rmap[u]].update(rmap[v] for v in dr[u])
            for u in range(nl):
                assert reach(joint, lmap[u]) == {lmap[v] for v in reach(dl, u)}
                paths += 1
            for u in range(nr):
                assert reach(joint, rmap[u]) == {rmap[v] for v in reach(dr, u)}
                paths += 1
            cases += 1
    assert cases > 0
    return cases, paths


configurations = [(0, 1, 1), (1, 1, 1), (2, 1, 1), (2, 2, 0),
                  (2, 0, 2), (1, 2, 1), (1, 1, 2)]
checks = [validate(*args) for args in configurations]
# Agreement is necessary even when the common base is closed on both sides.
left = [set(), set()]
right = [{1}, set()]
assert reach([{1}, set()], 0) != reach(left, 0)
assert base_closed(left, 2) and base_closed(right, 2)
# Base closure is necessary even when the relations agree on the base.
left = [set(), set()]
right = [{1}, set()]
joined = [{2}, set(), set()]
assert agree_on_base(left, right, 1)
assert reach(joined, 0) != reach(left, 0)
print({'configurations': len(checks), 'admissible_diagrams': sum(c for c, _ in checks),
       'closure_equalities': sum(q for _, q in checks),
       'missing_agreement_and_closed_base_counterexamples': 2})
