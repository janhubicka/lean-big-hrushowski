#!/usr/bin/env python3
"""Independent small finite checks for canonical local N0 lex fibres.

Checks complete positive and negative directed adjacency matrices,
pointwise (rather than setwise) lower-part stabilizers, and independence
from the arbitrary base enumeration of vertices outside the lower part.
"""
from itertools import permutations, product


def orientations(n):
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for choices in product((0, 1, 2), repeat=len(pairs)):
        out = [set() for _ in range(n)]
        for (a, b), typ in zip(pairs, choices):
            if typ == 1:
                out[a].add(b)
            elif typ == 2:
                out[b].add(a)
        if all(len(row) <= 2 for row in out):
            yield tuple(frozenset(row) for row in out)


def reach(out, x):
    reached, todo = {x}, [x]
    while todo:
        for y in out[todo.pop()]:
            if y not in reached:
                reached.add(y)
                todo.append(y)
    return frozenset(reached)


def components(out):
    reaches = [reach(out, x) for x in range(len(out))]
    remaining, found = set(range(len(out))), []
    while remaining:
        x = min(remaining)
        part = frozenset(y for y in remaining if y in reaches[x] and x in reaches[y])
        assert part
        remaining.difference_update(part)
        found.append((part, frozenset().union(*(reaches[y] for y in part))))
    return found


def stabilizer_card(out, closure, lower):
    order = tuple(sorted(closure))
    ans = 0
    for p in permutations(order):
        m = dict(zip(order, p))
        if any(m[x] != x for x in lower):
            continue
        if all((y in out[x]) == (m[y] in out[m[x]])
               for x in order for y in order):
            ans += 1
    return ans


def lex_code(out, order):
    return tuple(int(y in out[x]) for x in order for y in order)


def check(out):
    n = len(out)
    classes = 0
    bases = 0
    for part, closure in components(out):
        lower = closure - part
        assert all(y in closure for x in closure for y in out[x])
        assert all(y in lower for x in lower for y in out[x])
        factor = stabilizer_card(out, closure, lower)
        assert factor >= 1
        order = tuple(sorted(closure))
        permlist = list(permutations(order))
        by_lower_key = {}
        for base in permlist:
            lower_key = tuple((i, x) for i, x in enumerate(base) if x in lower)
            fixed = [p for p in permlist if all(p[i] == x for i, x in lower_key)]
            assert fixed
            mincode = min(lex_code(out, p) for p in fixed)
            canonical = frozenset(p for p in fixed if lex_code(out, p) == mincode)
            assert len(canonical) == factor, (n, out, part, base, factor, len(canonical))
            assert all(all(p[i] == x for i, x in lower_key) for p in canonical)
            if lower_key in by_lower_key:
                assert canonical == by_lower_key[lower_key]
            else:
                by_lower_key[lower_key] = canonical
            bases += 1
        classes += len(by_lower_key)
    return classes, bases


def regressions():
    # Directed 3-cycle with incoming leaf: local stabilizer 3, global 1.
    tri_leaf = (frozenset({1}), frozenset({2}),
                frozenset({0}), frozenset({0}))
    assert stabilizer_card(tri_leaf, frozenset({0, 1, 2}), frozenset()) == 3
    assert stabilizer_card(tri_leaf, frozenset({0, 1, 2, 3}), frozenset()) == 1
    # Two sinks: pointwise fixing the lower pair differs from setwise fixing.
    fork = (frozenset({1, 2}), frozenset(), frozenset())
    assert stabilizer_card(fork, frozenset({0, 1, 2}), frozenset({1, 2})) == 1
    assert stabilizer_card(fork, frozenset({0, 1, 2}), frozenset({0})) == 2


def main():
    regressions()
    total_orientations, total_classes, total_bases = 0, 0, 0
    for n in range(0, 5):
        for out in orientations(n):
            classes, bases = check(out)
            total_orientations += 1
            total_classes += classes
            total_bases += bases
    print(f"PASS: {total_orientations} orientations, {total_classes} "
          f"ordered-lower-part classes, {total_bases} base enumerations; "
          "induced/global and pointwise/setwise controls")


if __name__ == "__main__":
    main()
