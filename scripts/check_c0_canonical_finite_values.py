#!/usr/bin/env python3
"""Exhaustive finite C0 canonical block-index closure audit.

For every graph on at most four labelled vertices, and *every* assignment
of vertices to up to four chronological component indices, check that if
each old prefix is strong in the next, every set closed under complete
backward-reachability values is strong in the entire finite graph.

Unlike the previous regression, this does not choose a favoured
minimal-step enumeration: it tests all compatible chronologies,
including skipped/empty index positions and multi-vertex components.
"""
from itertools import combinations, product

def edges_of(n, mask):
    pairs = list(combinations(range(n), 2))
    return [pair for bit, pair in enumerate(pairs) if mask & (1 << bit)]

def delta(edges, vertices):
    return 2 * vertices.bit_count() - sum(
        bool(vertices & (1 << u)) and bool(vertices & (1 << v))
        for u, v in edges)

def strong(edges, a, b):
    if a & ~b:
        return False
    tail = b & ~a
    t = tail
    while True:
        if delta(edges, a | t) < delta(edges, a):
            return False
        if t == 0:
            return True
        t = (t - 1) & tail

def check_indexing(edges, labels, m):
    n = len(labels)
    blocks = [sum(1 << u for u, j in enumerate(labels) if j == k)
              for k in range(m)]
    prefixes = [0]
    for block in blocks:
        prefixes.append(prefixes[-1] | block)
    if not all(strong(edges, prefixes[k], prefixes[k+1])
               for k in range(m)):
        return 0, 0
    assert prefixes[-1] == (1 << n) - 1
    dependencies = [set() for _ in range(m)]
    for u, v in edges:
        i, j = labels[u], labels[v]
        if i > j:
            dependencies[i].add(j)
        elif j > i:
            dependencies[j].add(i)
    closure_values = [0] * m
    for i in range(m):
        reached, frontier = {i}, [i]
        for component in frontier:
            for old in dependencies[component]:
                if old not in reached:
                    reached.add(old)
                    frontier.append(old)
        closure_values[i] = 0
        for component in reached:
            closure_values[i] |= blocks[component]
        assert (closure_values[i] & blocks[i]) == blocks[i]
    tested = 0
    for selected in range(1 << n):
        if all(closure_values[labels[u]] & ~selected == 0
               for u in range(n) if selected & (1 << u)):
            assert strong(edges, selected, prefixes[-1]), (
                "failed", n, edges, labels, selected)
            tested += 1
    return 1, tested

graphs = sequences = closed_subsets = empty_components = 0
for n in range(5):
    for bits in range(1 << (n*(n-1)//2)):
        edges = edges_of(n, bits)
        graphs += 1
        for m in range(1, 5):
            for labels in product(range(m), repeat=n):
                counted, closed = check_indexing(edges, labels, m)
                sequences += counted
                closed_subsets += closed
                if counted and set(labels) != set(range(m)):
                    empty_components += 1

assert sequences > 0 and closed_subsets > 0 and empty_components > 0
print({"labelled_graphs": graphs,
       "strong_indexed_presentations": sequences,
       "unary_closed_subsets_strong": closed_subsets,
       "presentations_with_empty_components": empty_components})
