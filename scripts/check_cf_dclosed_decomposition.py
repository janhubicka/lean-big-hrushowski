#!/usr/bin/env python3
"""Bounded adversarial tests of finite strict d-closed decomposition.

Check all labelled simple graphs with 0..5 vertices and all finite
substructure inclusions a ⊆ b. For every a <=_d b:
- the smallest proper d-closed intermediate produces a finite chain;
- every chain step is a minimal strict d-closed extension;
- the minimal-step criterion agrees with the closure of every new
  generator in the finite ambient endpoint b;
- d-closed hulls are the least closed supersets of their generators.

These are finite diagnostics, not general Lean proof certificates.
"""
from itertools import combinations
from functools import lru_cache

pairs_checked = dclosed_pairs = minimal_steps = chains = hulls = 0

def graph_check(n, edges):
    global pairs_checked, dclosed_pairs, minimal_steps, chains, hulls
    N = 1 << n

    delta = tuple(2*s.bit_count() - sum(
        bool(s & (1 << u)) and bool(s & (1 << v)) for u,v in edges)
        for s in range(N))

    @lru_cache(None)
    def is_dclosed(a, b):
        if a & ~b:
            return False
        tail = b & ~a
        sub = tail
        while sub:
            if delta[a] >= delta[a | sub]:
                return False
            sub = (sub - 1) & tail
        return True

    @lru_cache(None)
    def hull(a, b):
        assert a & ~b == 0
        candidates = [
            c for c in range(N) if c & ~b == 0
            and a & ~c == 0 and is_dclosed(c, b)
        ]
        assert candidates
        h = b
        for c in candidates:
            h &= c
        assert is_dclosed(h, b)
        assert a & ~h == 0
        assert all(h & ~c == 0 for c in candidates)
        return h

    def minimal_step(a, b):
        if a == b or not is_dclosed(a, b):
            return False
        for c in range(N):
            if c != a and c != b and a & ~c == 0 and c & ~b == 0:
                if is_dclosed(c, b):
                    return False
        return True

    def factor(a, b):
        stages = [a]
        while a != b:
            candidates = [
                c for c in range(N) if c != a and a & ~c == 0
                and c & ~b == 0 and is_dclosed(c, b)
            ]
            c = min(candidates, key=lambda c: (c.bit_count(), c))
            assert minimal_step(a, c)
            assert is_dclosed(c, b)
            stages.append(c)
            a = c
        assert len(stages) <= n+1
        return stages

    for b in range(N):
        sub = b
        while True:
            a = sub
            pairs_checked += 1
            if is_dclosed(a, b):
                dclosed_pairs += 1
                stages = factor(a, b)
                assert stages[0] == a and stages[-1] == b
                assert all(stages[i] != stages[i+1] for i in
                           range(len(stages)-1))
                chains += 1
                condition = all(hull(a | (1 << x), b) == b
                                for x in range(n)
                                if b & (1 << x) and not a & (1 << x))
                assert minimal_step(a, b) == (a != b and condition)
                if minimal_step(a, b):
                    minimal_steps += 1
            # Test least-hull properties for every possible generator,
            # even when a itself is not d-closed in b.
            h = hull(a, b)
            assert a & ~h == 0
            assert is_dclosed(h, b)
            hulls += 1
            if not sub:
                break
            sub = (sub - 1) & b

for n in range(6):
    possible = tuple(combinations(range(n), 2))
    for edge_mask in range(1 << len(possible)):
        E = tuple(edge for j,edge in enumerate(possible)
                  if edge_mask & (1 << j))
        graph_check(n, E)

# A genuine non-singleton minimal d-closed step:
# empty -> K4, and the same K4 freely attached over an isolated old p.
for old in (0, 1 << 4):
    n = 5
    E = tuple(combinations(range(4), 2))
    delta = lambda s: 2*s.bit_count()-sum(
        s & (1<<u) != 0 and s & (1<<v) != 0 for u,v in E)
    b = old | ((1 << 4) - 1)
    assert delta[b] > delta[old]
    for sub in range(1, 1<<4):
        c = old | sub
        assert delta[c] > delta[old]

print({
    "graphs_up_to_vertices":5,
    "finite_inclusions_checked":pairs_checked,
    "dclosed_inclusions":dclosed_pairs,
    "minimal_dclosed_steps":minimal_steps,
    "dclosed_chains":chains,
    "least_hulls_checked":hulls,
    "intermediate_or_generator_mismatches":0,
    "four_vertex_minimal_increment":True
})
