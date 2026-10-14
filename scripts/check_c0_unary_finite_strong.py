#!/usr/bin/env python3
"""Finite adversarial regression for complete component unary closures.

Enumerate all labelled simple graphs of at most five vertices, factor
their empty-to-whole strong inclusion into minimal strong blocks, and
construct the full set-valued unary function by back-edge reachability.
Every function-closed finite subset must be graph-strong.

Two K4 examples show why BOTH closure requirements are needed:
including an entire component and including all its old neighbours.
"""

def graph_edges(n, mask):
    pairs = [(i, j) for j in range(n) for i in range(j)]
    return {(i,j) for k,(i,j) in enumerate(pairs) if mask & (1<<k)}


def delta(edges, s):
    return 2*s.bit_count() - sum(
        bool(s & (1<<u)) and bool(s & (1<<v)) for u,v in edges)


def strong(edges, a, b):
    if a & ~b: return False
    rest = b & ~a
    z = rest
    while True:
        if delta(edges, a) > delta(edges, a|z): return False
        if z == 0: return True
        z = (z-1)&rest


def minimal(edges, a, b):
    if a == b or not strong(edges,a,b): return False
    rest = b & ~a
    z = rest
    while True:
        c = a|z
        if c not in (a,b) and strong(edges,c,b): return False
        if z == 0: return True
        z = (z-1)&rest


def blocks_of(edges, full):
    a = 0
    blocks = []
    while a != full:
        candidates = [z for z in range(full+1)
                      if z & ~full == 0 and z & a == a
                      and z != a and strong(edges,z,full)]
        assert candidates
        b = min(candidates, key=lambda z:(z.bit_count(),z))
        assert minimal(edges,a,b)
        blocks.append(b & ~a)
        a = b
    return blocks


def function_values(edges, blocks, n):
    component_of = {}
    for i, block in enumerate(blocks):
        for u in range(n):
            if block & (1<<u):
                assert u not in component_of
                component_of[u] = i
    assert len(component_of) == n
    dep = [set() for _ in blocks]
    for u,v in edges:
        i,j = component_of[u],component_of[v]
        if i>j: dep[i].add(j)
        if j>i: dep[j].add(i)
    closure = {}
    for i in range(len(blocks)):
        reachable, queue = {i}, [i]
        for j in queue:
            for k in dep[j]:
                if k not in reachable:
                    reachable.add(k)
                    queue.append(k)
        value = 0
        for k in reachable: value |= blocks[k]
        closure[i] = value
    return {u:closure[component_of[u]] for u in range(n)}


graphs = closed_sets = block_steps = 0
for n in range(6):
    full = (1<<n)-1
    for mask in range(1 << (n*(n-1)//2)):
        edges = graph_edges(n,mask)
        assert strong(edges,0,full)
        blocks = blocks_of(edges,full)
        values = function_values(edges,blocks,n)
        block_steps += len(blocks)
        for s in range(1<<n):
            if all(values[u] & ~s == 0 for u in range(n)
                   if s & (1<<u)):
                assert strong(edges,s,full), (n,mask,blocks,s)
                closed_sets += 1
        graphs += 1

# In K4, {a} < {a,x,y,z} is minimal strong. The new block is
# B={x,y,z}; retaining only two new vertices violates whole-block
# closure even though the old neighbour a is retained.
k4 = graph_edges(4, (1<<6)-1)
assert minimal(k4,1,15)
partial = 0b0111
assert not strong(k4,partial,15)
# Retaining the entire new block but omitting its one old
# neighbour a also fails graph strongness.
tail = 0b1110
assert not strong(k4,tail,15)
print({"labelled_graphs":graphs, "minimal_strong_blocks":block_steps,
       "unary_closed_subsets_strong":closed_sets,
       "whole_block_counterexample":1, "old_neighbour_counterexample":1})
