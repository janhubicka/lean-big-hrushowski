"""Independent finite adversarial regressions for Big Hrushovski Track F.
Does not import manuscript verification code.  Not an infinite Ramsey proof.
"""
from itertools import combinations, permutations, product
from math import ceil, factorial, log
import json


def bits(mask):
    return [i for i in range(mask.bit_length()) if mask >> i & 1]


def delta(out, mask):
    edges = {tuple(sorted((x, y))) for x, s in enumerate(out) for y in bits(s)}
    return 2 * mask.bit_count() - sum(bool(mask >> a & 1 and mask >> b & 1)
                                       for a, b in edges)


def threshold(n):
    return (0, 2, 3, 4, 5)[n] if n < 5 else ceil(5 + log(n / 5))


def d_closed(out, base):
    all_vertices = (1 << len(out)) - 1
    remaining = all_vertices ^ base
    ext = remaining
    while ext:
        if delta(out, base | ext) <= delta(out, base):
            return False
        ext = (ext - 1) & remaining
    return True


def successor_closed(out, base):
    return all((out[v] & ~base) == 0 for v in bits(base))


def cf_membership(out):
    n = len(out)
    if any(s.bit_count() > 2 or s >> x & 1 for x, s in enumerate(out)):
        return False
    if any(x in bits(out[y]) for x, s in enumerate(out) for y in bits(s)):
        return False
    return all(delta(out, mask) >= threshold(mask.bit_count())
               for mask in range(1 << n))


def n0_formula(out):
    n = len(out)
    reach = [(1 << v) | s for v, s in enumerate(out)]
    for k in range(n):
        for v in range(n):
            if reach[v] >> k & 1:
                reach[v] |= reach[k]
    unassigned = set(range(n))
    components = []
    while unassigned:
        v = min(unassigned)
        component = tuple(w for w in sorted(unassigned)
                          if reach[v] >> w & 1 and reach[w] >> v & 1)
        components.append(component)
        unassigned.difference_update(component)
    component_of = {v: i for i, comp in enumerate(components) for v in comp}
    dependencies = {
        i: {component_of[v] for v in bits(reach[comp[0]]) if v not in comp}
        for i, comp in enumerate(components)
    }
    ell = 0
    for ordering in permutations(range(len(components))):
        earlier = set()
        for i in ordering:
            if not dependencies[i] <= earlier:
                break
            earlier.add(i)
        else:
            ell += 1
    stabilizers = []
    for comp in components:
        lower = set(bits(reach[comp[0]])) - set(comp)
        local = sorted(lower | set(comp))
        count = 0
        for choice in permutations(comp):
            f = {x: y for x, y in zip(comp, choice)} | {x: x for x in lower}
            if all(bool(out[x] >> y & 1) == bool(out[f[x]] >> f[y] & 1)
                   for x in local for y in local):
                count += 1
        stabilizers.append(count)
    degree = ell
    for count in stabilizers:
        degree *= count
    return degree, ell, stabilizers


def audit_n0():
    count = 0
    for n in range(5):
        for choices in product((0, 1, 2), repeat=n*(n-1)//2):
            out = [0] * n
            for (a, b), direction in zip(combinations(range(n), 2), choices):
                if direction == 1:
                    out[a] |= 1 << b
                if direction == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            assert n0_formula(out)[0] <= factorial(n)
            count += 1
    cases = {
        "empty": ((), 1),
        "fork": ((0b110, 0, 0), 2),
        "three_cycle": ((0b010, 0b100, 0b001), 3),
        "incoming_leaf": ((0b010, 0b100, 0b001, 0b001), 3),
        "outgoing_leaf": ((0b1010, 0b100, 0b001, 0), 1),
    }
    outputs = {}
    for label, (out, expected) in cases.items():
        degree, ell, kernels = n0_formula(out)
        assert degree == expected, (label, degree, expected)
        outputs[label] = {"degree": degree, "ell": ell, "kernels": kernels}
    return {"orientations_up_to_four": count, "examples": outputs}


def audit_nf():
    # Two sinks plus a common predecessor: strong but not strictly d-closed.
    one = (0, 0, 0b011)
    assert cf_membership(one)
    assert delta(one, 0b011) == delta(one, 0b111) == 4
    assert not d_closed(one, 0b011)
    # Two common predecessors create a four-cycle, forbidden by q(4)=5.
    two = (0, 0, 0b011, 0b011)
    assert delta(two, 0b1111) == 4 < threshold(4)
    # Three and four roots with all proper sink subsets closed.
    gadgets = {}
    for r in (3, 4):
        n = 3 * r
        out = [0] * n
        for i in range(2 * r):
            out[r + i] = (1 << (r + (i+1) % (2*r))) | (1 << (i % r))
        assert cf_membership(out)
        roots = (1 << r) - 1
        for s in range(roots):
            assert successor_closed(out, s) and d_closed(out, s), (r, s)
        assert successor_closed(out, roots) and not d_closed(out, roots)
        assert delta(out, roots) == delta(out, (1 << n) - 1) == 2 * r
        gadgets[r] = {"size": n, "proper_closed_sink_sets": roots}
    for n in range(1, 20001):
        assert threshold(n+1) <= threshold(n)+1
        if n >= 5:
            assert threshold(2*n+1) <= threshold(n)+2
    return {"higher_root_gadgets": gadgets, "growth_samples": 20000}


if __name__ == "__main__":
    print(json.dumps({"status": "PASS", "scope": "finite diagnostics only",
                      "N0": audit_n0(), "NF": audit_nf()}, indent=2))
