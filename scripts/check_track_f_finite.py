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


def audit_nf_star_extensions():
    """Exhaust 2-oriented C_F sources through four vertices, and all subsets of sinks."""
    old_count = 0
    orientation_count = 0
    extension_count = 0
    subset_count = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for graph_mask in range(1 << len(pairs)):
            edges = tuple(pair for i, pair in enumerate(pairs) if graph_mask >> i & 1)
            old = [0] * n
            for a, b in edges:
                old[a] |= 1 << b
                old[b] |= 1 << a
            old_delta = delta_from_adjacency(old)
            if any(d < threshold(mask.bit_count()) for mask, d in enumerate(old_delta)):
                continue
            old_count += 1
            for directions in product((0, 1), repeat=len(edges)):
                outgoing = [0] * n
                for (a, b), direction in zip(edges, directions):
                    outgoing[a if direction else b] |= 1 << (b if direction else a)
                if any(s.bit_count() > 2 for s in outgoing):
                    continue
                orientation_count += 1
                sinks = sum(1 << i for i, s in enumerate(outgoing) if not s)
                chosen = sinks
                while True:
                    picked = bits(chosen)
                    z = n
                    star = old + [0] * (1 + len(picked))
                    for new_vertex, a in enumerate(picked, n + 1):
                        star[new_vertex] |= (1 << z) | (1 << a)
                        star[z] |= 1 << new_vertex
                        star[a] |= 1 << new_vertex
                    ds = delta_from_adjacency(star)
                    assert all(d >= threshold(mask.bit_count()) for mask, d in enumerate(ds))
                    full_old = (1 << n) - 1
                    for new_mask in range(1, 1 << (len(star) - n)):
                        assert ds[full_old | (new_mask << n)] > old_delta[full_old]
                    extension_count += 1
                    subset_count += len(ds)
                    if chosen == 0:
                        break
                    chosen = (chosen - 1) & sinks
    return dict(old_graphs=old_count, old_orientations=orientation_count,
                strict_star_extensions=extension_count, induced_subsets=subset_count)


def delta_from_adjacency(adj):
    result = [0] * (1 << len(adj))
    for mask in range(1, len(result)):
        bit = mask & -mask
        v = bit.bit_length() - 1
        prev = mask ^ bit
        result[mask] = result[prev] + 2 - (adj[v] & prev).bit_count()
    return result


def audit_successor_closed_strong():
    """Independent exhaustive edge counting, including a nonclosed counterexample."""
    checks = 0
    for n in range(5):
        for choices in product((0, 1, 2), repeat=n * (n - 1) // 2):
            outgoing = [0] * n
            for (a, b), choice in zip(combinations(range(n), 2), choices):
                if choice == 1:
                    outgoing[a] |= 1 << b
                elif choice == 2:
                    outgoing[b] |= 1 << a
            if any(s.bit_count() > 2 for s in outgoing):
                continue
            for s in range(1 << n):
                if not successor_closed(outgoing, s):
                    continue
                for t in range(1 << n):
                    if s & t != s:
                        continue
                    assert delta(outgoing, s) <= delta(outgoing, t)
                    checks += 1
    # The hypothesis must not be deleted: a regular tournament on K5
    # is a 2-orientation and {0} is not strong in the full graph.
    tournament = tuple((1 << ((i + 1) % 5)) | (1 << ((i + 2) % 5))
                       for i in range(5))
    assert all(v.bit_count() == 2 for v in tournament)
    assert all((tournament[a] >> b & 1) != (tournament[b] >> a & 1)
               for a, b in combinations(range(5), 2))
    assert not successor_closed(tournament, 1)
    assert delta(tournament, 1) == 2 > delta(tournament, 31) == 0
    return {"successor_closed_strong_checks": checks,
            "nonclosed_counterexample": "regular K5 tournament"}



def audit_reachability_and_components():
    """All finite successor closures and SCC partitions through four vertices."""
    instances = closure_cases = minimal_cases = component_cases = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for choices in product((0, 1, 2), repeat=len(pairs)):
            out = [0] * n
            for (a, b), choice in zip(pairs, choices):
                if choice == 1:
                    out[a] |= 1 << b
                elif choice == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            instances += 1
            reach = [(1 << x) | out[x] for x in range(n)]
            for k in range(n):
                for x in range(n):
                    if reach[x] >> k & 1:
                        reach[x] |= reach[k]
            def closure(s):
                value = 0
                for x in bits(s):
                    value |= reach[x]
                return value
            for s in range(1 << n):
                c = closure(s)
                assert s & c == s
                assert successor_closed(out, c)
                assert closure(c) == c
                for t in range(1 << n):
                    if s & t == s and successor_closed(out, t):
                        assert c & t == c
                        minimal_cases += 1
                closure_cases += 1
            for x in range(n):
                cx = sum(1 << y for y in range(n)
                         if reach[x] >> y & 1 and reach[y] >> x & 1)
                for y in range(n):
                    cy = sum(1 << z for z in range(n)
                             if reach[y] >> z & 1 and reach[z] >> y & 1)
                    mutual = bool(reach[x] >> y & 1 and reach[y] >> x & 1)
                    assert (cx == cy) == mutual
                    component_cases += 1
    return {"orientations": instances,
            "closure_cases": closure_cases,
            "closure_minimality_cases": minimal_cases,
            "component_pair_cases": component_cases}


if __name__ == "__main__":
    print(json.dumps({"status": "PASS", "scope": "finite diagnostics only",
                      "N0": audit_n0(), "NF": audit_nf(),
                      "successor_closed_strong": audit_successor_closed_strong(),
                      "reachability": audit_reachability_and_components(),
                      "NF_star_extensions": audit_nf_star_extensions()}, indent=2))
