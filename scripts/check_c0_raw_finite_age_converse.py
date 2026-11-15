#!/usr/bin/env python3
"""Cross-presentation adversarial regression for the raw C0 finite-age converse.

Generated roots may come from DIFFERENT finite C0 presentations and
may have identical pointed coordinates but incompatible complete
E/C matrices. Their raw one-generated closures are amalgamated
literally as sets of full codes. The induced finite graph and complete
unary values must then admit an empty-or-minimal-strong component
index. This is a small finite semantic check, not a Lean proof.

Tests both pairs and triples of independent roots, empty generators,
all edges/nonedges in each union, full C-values and all induced
predimensions. The component index is constructed from the complete
mutual-generation classes, not from coordinate labels or roots.
"""
from itertools import combinations
from check_c0_raw_host_full_relabel import sample, closed, adj
from check_c0_coordinate_host_finite import (
    finite_component_values, finite_predim, finite_subsets,
    finite_minimal_step,
)


def canonical_blocks(vertices):
    """Order full C-equivalence classes by complete closure size.

    Any genuine dependency must strictly decrease closure size;
    mutually generating roots stay in the same block. Independent
    components may be ordered arbitrarily. Each vertex is a full
    code, never just its natural-number pointed coordinate.
    """
    # The blocks are equivalence classes of MUTUAL generators:
    # q and r lie in the same block iff closed(q) == closed(r).
    # Do NOT take each entire closed(q) as a block: it also includes
    # proper ancestor components and would overwrite their labels.
    classes = {}
    for q in vertices:
        classes.setdefault(closed(q), set()).add(q)
    assert all(C <= vertices for C in classes)
    ordered = sorted(classes.values(), key=lambda B: (
        len(closed(next(iter(B)))), tuple(sorted(repr(q) for q in B))))
    position = {q: i for i, B in enumerate(ordered) for q in B}
    assert len(position) == len(vertices)
    return ordered, position


def verify(generators):
    union = frozenset(r for q in generators for r in closed(q))
    assert all(q in union for q in generators)
    assert all(closed(q) <= union for q in union)
    listed = sorted(union, key=repr)
    idx = {q: i for i, q in enumerate(listed)}
    edges = {(idx[q], idx[r]) for q, r in combinations(listed, 2)
             if adj(q, r)}
    assert all(adj(q, r) == adj(r, q) for q in listed for r in listed)
    assert all(not adj(q, q) for q in listed)
    for s in finite_subsets(frozenset(range(len(listed)))):
        assert finite_predim(s, edges) >= 0, (
            "non-two-sparse finite raw union", generators, s)
    classes, position = canonical_blocks(union)
    labels = tuple(position[q] for q in listed)
    for i, q in enumerate(listed):
        values = finite_component_values(labels, edges)
        named = frozenset(listed[j] for j in values[i])
        assert named == closed(q), (
            "incorrect whole C-value", generators, q, named, closed(q))
    for k in range(len(classes)):
        before = frozenset(i for i, q in enumerate(listed)
                           if position[q] < k)
        after = frozenset(i for i, q in enumerate(listed)
                          if position[q] < k + 1)
        assert finite_minimal_step(before, after, edges), (
            "not a minimal strong component extension",
            generators, k, before, after)
    return len(listed), len(classes), len(edges)


def main():
    pool, presentations = sample()
    assert presentations == 1401
    roots = sorted(pool, key=lambda q: (
        len(q[0]), q[1], repr(q[0]), repr(q[2]), repr(q[3])))
    assert len(roots) >= 100
    # Spread deterministic representatives across all support sizes
    # rather than testing only singleton codes.
    stride = max(1, len(roots) // 75)
    selected = roots[::stride][:100]
    assert len(selected) >= 70
    cases = [tuple()]
    cases += [(q,) for q in selected]
    # Cross-presentation combinations drawn from the WHOLE range
    # of support sizes, rather than mostly the smallest codes.
    m = len(selected)
    cases += [(selected[i % m], selected[(7 * i + 13) % m])
              for i in range(180)]
    cases += [(selected[i % m], selected[(11 * i + 7) % m],
               selected[(17 * i + 31) % m]) for i in range(90)]
    cases += [(roots[0], roots[-1]), (roots[len(roots)//2], roots[-1]),
              (roots[-1], roots[-2])]
    # Deliberately retain distinct COMPLETE codes with the same
    # pointed natural-number coordinate as a negative control to
    # identification by roots alone.
    same_point = {}
    for q in roots:
        if q[1] in same_point and same_point[q[1]] != q:
            cases.append((same_point[q[1]], q))
            break
        same_point[q[1]] = q
    verified = max_vertices = max_blocks = edges_total = 0
    coordinate_collisions = 0
    for gen in cases:
        for q, r in combinations(gen, 2):
            if q != r and q[1] == r[1]:
                coordinate_collisions += 1
        n, k, e = verify(gen)
        verified += 1
        max_vertices = max(n, max_vertices)
        max_blocks = max(k, max_blocks)
        edges_total += e
    assert coordinate_collisions > 0
    print("PASS raw C0 cross-presentation finite-age converse: "
          f"{presentations} finite source presentations, "
          f"{len(pool)} actual raw code vertices, "
          f"{verified} independent generating families, "
          f"max {max_vertices} raw vertices and {max_blocks} components, "
          f"{edges_total} total induced edges, "
          f"{coordinate_collisions} same-coordinate generator pairs; "
          "full E/nonedges, complete C, two-sparseness, "
          "minimal-strong canonical component indexes")


if __name__ == "__main__":
    main()
