"""Independent exhaustive test of the finite strong response with forced growth.

All graph pairs on at most three vertices, all induced strong source
embeddings of at most two vertices, and every compatible diagram are
examined. A free amalgam is formed over the source and then one isolated
vertex is added. Verify both induced embeddings, exact base labels,
two-sparsity, strongness of both images, strict growth and no label gaps.
This is a diagnostic, not a substitute for the Lean proof.
"""
from itertools import combinations, permutations


def graphs(n):
    pairs = tuple(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        yield frozenset(p for i, p in enumerate(pairs) if mask & (1 << i))


def subsets(vertices):
    vertices = list(vertices)
    for mask in range(1 << len(vertices)):
        yield frozenset(vertices[i] for i in range(len(vertices)) if mask & (1 << i))


def predim(edges, vertices):
    vertices = set(vertices)
    return 2 * len(vertices) - sum(x in vertices and y in vertices for x, y in edges)


def sparse(edges, n):
    return all(predim(edges, t) >= 0 for t in subsets(range(n)))


def strong(edges, base, n):
    base = frozenset(base)
    return all(predim(edges, base) <= predim(edges, t)
               for t in subsets(range(n)) if base <= t)


def adjacent(edges, x, y):
    return x != y and tuple(sorted((x, y))) in edges


def check(c, b, p, ec, eb, f, g):
    labels = dict(zip(g, f))
    tail = [x for x in range(b) if x not in labels]
    for i, x in enumerate(tail):
        labels[x] = c + i
    size = c + len(tail) + 1
    fresh = size - 1
    e = set(ec)
    for x, y in eb:
        e.add(tuple(sorted((labels[x], labels[y]))))
    e = frozenset(e)
    assert set(range(size)) == set(range(c)) | set(labels.values()) | {fresh}
    assert size > c and fresh not in range(c) and fresh not in labels.values()
    assert all(adjacent(ec, x, y) == adjacent(e, x, y)
               for x in range(c) for y in range(c))
    assert all(adjacent(eb, x, y) == adjacent(e, labels[x], labels[y])
               for x in range(b) for y in range(b))
    assert all(labels[g[x]] == f[x] for x in range(p))
    assert sparse(e, size)
    assert strong(e, range(c), size)
    assert strong(e, labels.values(), size)


checked = 0
for c in range(4):
    for b in range(4):
        for p in range(min(c, b, 2) + 1):
            for ec in graphs(c):
                if not sparse(ec, c):
                    continue
                for eb in graphs(b):
                    if not sparse(eb, b):
                        continue
                    for f in permutations(range(c), p):
                        if not strong(ec, f, c):
                            continue
                        for g in permutations(range(b), p):
                            if not strong(eb, g, b):
                                continue
                            if any(adjacent(ec, f[i], f[j]) != adjacent(eb, g[i], g[j])
                                   for i in range(p) for j in range(p)):
                                continue
                            check(c, b, p, ec, eb, f, g)
                            checked += 1

# Negative control: two 2-sparse K5 graphs joined over a nonstrong K3.
k5 = frozenset(combinations(range(5), 2))
assert sparse(k5, 5) and not strong(k5, range(3), 5)
bad = frozenset(set(k5) | {(x + 2, y + 2) for x, y in k5})
assert len(bad) == 17 and predim(bad, range(7)) == -3

print(f"Checked {checked:,} compatible finite growing strong response diagrams.")
print("Negative K5-over-K3 strongness control passed.")
