#!/usr/bin/env python3
"""Independent finite test of the C0 functional-reduct lifting argument.

For small strong graph spans A≤C and A≤B, form D=C ⊕_A B.
Test free-amalgam sparsity and factor strongness, refine ∅≤C≤D into
minimal strong blocks, and verify that appending blocks does not change
old unary closures. Every finite set closed under the resulting unary
function must be strong in D.

These are diagnostic checks, not a proof of a countable Fraïssé limit.
"""
from itertools import product


def edges_of(n):
    return [(u, v) for v in range(n) for u in range(v)]


def graph(n, mask):
    return {uv for k, uv in enumerate(edges_of(n)) if mask & (1 << k)}


def delta(edges, s):
    return 2 * s.bit_count() - sum(
        bool(s & (1 << u)) and bool(s & (1 << v)) for u, v in edges)


def sparse(edges, n):
    return all(delta(edges, s) >= 0 for s in range(1 << n))


def strong(edges, a, b):
    if a & ~b:
        return False
    tail, sub = b & ~a, b & ~a
    while True:
        if delta(edges, a | sub) < delta(edges, a):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & tail


def minimal(edges, a, b):
    if a == b or not strong(edges, a, b):
        return False
    tail, sub = b & ~a, b & ~a
    while True:
        c = a | sub
        if c != a and c != b and strong(edges, c, b):
            return False
        if sub == 0:
            return True
        sub = (sub - 1) & tail


def minimal_blocks(edges, a, b):
    assert strong(edges, a, b)
    blocks = []
    while a != b:
        choices = [z for z in range(1 << b.bit_length())
                   if z & b == z and z & a == a and z != a
                   and strong(edges, z, b)]
        next_a = min(choices, key=lambda z: (z.bit_count(), z))
        assert minimal(edges, a, next_a)
        blocks.append(next_a ^ a)
        a = next_a
    return blocks


def unary_closures(edges, blocks, n):
    comp = {v: i for i, block in enumerate(blocks)
            for v in range(n) if (block >> v) & 1}
    assert len(comp) == n
    previous = {}
    for u, iu in comp.items():
        previous.setdefault(iu, set())
        for v, iv in comp.items():
            if iv < iu and (min(u, v), max(u, v)) in edges:
                previous[iu].add(iv)
    closure = {}
    for i in range(len(blocks)):
        reached, queue = {i}, [i]
        for j in queue:
            for k in previous[j]:
                if k not in reached:
                    reached.add(k)
                    queue.append(k)
        close_i = 0
        for j in reached:
            close_i |= blocks[j]
        closure[i] = close_i
    return {v: closure[i] for v, i in comp.items()}


configs = [(p, l, r) for p, l, r in
           product(range(3), range(3), range(1, 4))
           if p + l + r <= 5]
cases = closed_subset_checks = closure_checks = 0
for p, l, r in configs:
    nc, nb, nt = p + l, p + r, p + l + r
    a = (1 << p) - 1
    c = (1 << nc) - 1
    b = (1 << nb) - 1
    full = (1 << nt) - 1
    right_map = tuple(range(p)) + tuple(p + l + i for i in range(r))
    for gm in range(1 << len(edges_of(nc))):
        ec = graph(nc, gm)
        if not sparse(ec, nc) or not strong(ec, a, c):
            continue
        for hm in range(1 << len(edges_of(nb))):
            eb = graph(nb, hm)
            if not sparse(eb, nb) or not strong(eb, a, b):
                continue
            if {uv for uv in ec if uv[1] < p} != \
               {uv for uv in eb if uv[1] < p}:
                continue
            joined = ec | {
                tuple(sorted((right_map[u], right_map[v])))
                for u, v in eb
            }
            assert sparse(joined, nt)
            assert strong(joined, c, full)
            image_b = sum(1 << right_map[v] for v in range(nb))
            assert strong(joined, image_b, full)
            old_blocks = minimal_blocks(ec, 0, c)
            new_blocks = minimal_blocks(joined, c, full)
            before = unary_closures(ec, old_blocks, nc)
            after = unary_closures(joined, old_blocks + new_blocks, nt)
            for v in range(nc):
                assert before[v] == after[v]
                closure_checks += 1
            for s in range(1 << nt):
                if all(after[v] & ~s == 0 for v in range(nt) if s >> v & 1):
                    assert strong(joined, s, full), (
                        "closed subset not strong", p, l, r, ec, eb, s)
                    closed_subset_checks += 1
            cases += 1

assert cases > 0 and closed_subset_checks > 0
print({"tagged_graph_spans": cases, "closed_subsets_strong": closed_subset_checks,
       "old_unary_values_unchanged": closure_checks,
       "parameter_configurations": len(configs)})
