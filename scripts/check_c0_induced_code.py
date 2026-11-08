#!/usr/bin/env python3
"""Finite adversarial checks of literal pointed code = induced-subtype code.

All reflexive/transitive complete unary closures and all compatible simple
graphs on 1..3 vertices, all chosen increasing label maps into n+2, every
original root, and every nonempty induced subset with a new root.

Crucially we test *nonclosed* subsets as well: the induced code identity
does not require closure, but equality with ambient complete unary values
DOES. These are regressions, not a Lean proof of the countable host W.
"""
from itertools import combinations, product


def closures(n):
    for raw in product(range(1 << n), repeat=n):
        c = [{j for j in range(n) if raw[i] & (1 << j)}
             for i in range(n)]
        if all(i in c[i] for i in range(n)) and all(
            c[j] <= c[i] for i in range(n) for j in c[i]
        ):
            yield c


def graphs(n):
    edges = list(combinations(range(n), 2))
    for bits in range(1 << len(edges)):
        yield {e for i, e in enumerate(edges) if bits & (1 << i)}


def code(domain, root, labels, closure, edges):
    return (
        frozenset(labels[u] for u in domain),
        labels[root],
        frozenset(
            (labels[u], labels[v])
            for u in domain for v in domain
            if tuple(sorted((u, v))) in edges
        ),
        frozenset(
            (labels[u], labels[v])
            for u in domain for v in domain
            if v in closure[u]
        ),
    )


def restrict_code(q, support, root_label):
    support = frozenset(support)
    assert support <= q[0] and root_label in support
    return (
        support,
        root_label,
        frozenset((a, b) for a, b in q[2]
                  if a in support and b in support),
        frozenset((a, b) for a, b in q[3]
                  if a in support and b in support),
    )


def main():
    structures = diagrams = induced = generated = nonclosed = 0
    for n in range(1, 4):
        for closure in closures(n):
            for edges in graphs(n):
                if not all(v in closure[u] or u in closure[v]
                           for u, v in edges):
                    continue
                structures += 1
                for labs in combinations(range(n + 2), n):
                    e = dict(enumerate(labs))
                    for old_root in range(n):
                        q = code(set(range(n)), old_root, e, closure, edges)
                        diagrams += 1
                        for mask in range(1, 1 << n):
                            s = {i for i in range(n) if mask & (1 << i)}
                            cs = {e[i] for i in s}
                            if any(not closure[i] <= s for i in s):
                                nonclosed += 1
                            for new_root in s:
                                left = restrict_code(q, cs, e[new_root])
                                right = code(s, new_root, e, closure, edges)
                                assert left == right
                                induced += 1
                        s = closure[old_root]
                        assert restrict_code(q, {e[i] for i in s},
                                             e[old_root]) == code(
                            s, old_root, e, closure, edges)
                        generated += 1

    assert (structures, diagrams, induced, generated, nonclosed) == (
        155, 4497, 53259, 4497, 18096
    ), (structures, diagrams, induced, generated, nonclosed)

    # Nonclosed finite restriction is an induced code but not a complete
    # substructure: the image of C(0) can lose vertex 1.
    c = [{0, 1}, {1}]
    q = code({0, 1}, 0, {0: 2, 1: 4}, c, set())
    cut = restrict_code(q, {2}, 2)
    assert cut[3] != q[3]
    assert (2, 4) in q[3] and (2, 4) not in cut[3]

    # The original root is independent of a restriction's new root.
    assert restrict_code(q, {4}, 4) == code(
        {1}, 1, {0: 2, 1: 4}, c, set())
    assert q[1] == 2 and restrict_code(q, {4}, 4)[1] == 4

    print(
        f"PASS {structures} systems, {diagrams} pointed parent codes, "
        f"{induced} exact induced subcodes, {generated} generated cuts "
        f"({nonclosed} nonclosed subset cases), and negative controls"
    )


if __name__ == "__main__":
    main()
