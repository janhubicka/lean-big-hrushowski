"""Adversarial audit of local-vs-ambient component automorphism groups.

Enumerates all oriented simple graphs on at most four vertices with
out-degree at most two. Checks invariance across generators of the
same SCC, successor-closedness of P_B, and explicit examples where
using global or merely setwise automorphisms gives a wrong factor.
"""
from itertools import combinations, permutations, product
import json


def automorphisms(out, vertices, fixed=(), setwise=False):
    vertices = tuple(vertices)
    fixed = set(fixed)
    count = 0
    for images in permutations(vertices):
        mp = dict(zip(vertices, images))
        if setwise:
            if {mp[v] for v in fixed} != fixed:
                continue
        elif any(mp[v] != v for v in fixed):
            continue
        if all(bool(out[v] >> w & 1) ==
               bool(out[mp[v]] >> mp[w] & 1)
               for v in vertices for w in vertices):
            count += 1
    return count


def component_data(out, x):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    comp = tuple(i for i in range(n)
                 if reach[x] >> i & 1 and reach[i] >> x & 1)
    closure = tuple(i for i in range(n) if reach[x] >> i & 1)
    lower = tuple(i for i in closure if i not in comp)
    return comp, closure, lower


def audit():
    orientations = components = generators = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for directions in product((0, 1, 2), repeat=len(pairs)):
            out = [0] * n
            for (x, y), direction in zip(pairs, directions):
                if direction == 1:
                    out[x] |= 1 << y
                elif direction == 2:
                    out[y] |= 1 << x
            if any(x.bit_count() > 2 for x in out):
                continue
            orientations += 1
            seen = set()
            for x in range(n):
                B, C, P = component_data(out, x)
                if B in seen:
                    continue
                seen.add(B)
                components += 1
                assert all(not (out[v] & ~sum(1 << y for y in P))
                           for v in P)
                local_g = automorphisms(out, C, P)
                assert local_g >= 1
                for y in B:
                    assert component_data(out, y) == (B, C, P)
                    assert automorphisms(out, C, P) == local_g
                    generators += 1
    cycle = [0b010, 0b100, 0b001]
    incoming_leaf = [0b010, 0b100, 0b001, 0b001]
    outgoing_leaf = [0b1010, 0b100, 0b001, 0]
    fork = [0, 0, 0b011]
    assert automorphisms(cycle, (0, 1, 2)) == 3
    assert automorphisms(incoming_leaf, (0, 1, 2)) == 3
    assert automorphisms(incoming_leaf, range(4)) == 1
    assert automorphisms(outgoing_leaf, range(4), (3,)) == 1
    assert automorphisms(fork, range(3), (0, 1)) == 1
    assert automorphisms(fork, range(3), (0, 1), setwise=True) == 2
    return dict(status="PASS", orientations=orientations,
                distinct_components=components,
                component_generators=generators,
                negative_cases=[
                    "incoming leaf: local cycle factor 3, global factor 1",
                    "fork: pointwise lower stabilizer 1, setwise stabilizer 2"])


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
