#!/usr/bin/env python3
"""Adversarial complete unpointed-key and named J consistency on raw C0 codes.

Enumerates raw pointed codes from finite minimal-strong C0 presentations,
then compares unrelated actual code vertices, including duplicate pointed
coordinates, multivertex top components and negative E/C incidences.
"""
from check_c0_raw_host_full_relabel import sample, closed, back, adj


def key(q):
    S, _point, E, C = q
    return S, E, C


def main():
    pool, presentations = sample()
    codes = list(pool)
    assert presentations == 1401
    closures = {q:closed(q) for q in codes}
    J = {q:back(q) for q in codes}
    pairs = mutual = distinct_mutual = same_coordinate = graph_checks = 0
    for q in codes:
        for r in codes:
            pairs += 1
            hqr = r in closures[q]
            hrq = q in closures[r]
            if q[1] == r[1] and q != r:
                same_coordinate += 1
            if hqr and hrq:
                mutual += 1
                assert key(q) == key(r)
                if q != r:
                    distinct_mutual += 1
            assert (r in J[q]) == (hqr and adj(q,r))
            assert (r in J[q]) == (hqr and
                (q[1],r[1]) in q[2])
            graph_checks += 1
    assert same_coordinate > 0
    assert distinct_mutual > 0, "need a multivertex-top witness"
    # The named J value cannot be defined solely by coordinates:
    # many different complete codes share a pointed coordinate.
    assert len({q[1] for q in codes}) < len(codes)
    print(f"PASS raw mutual complete keys and J=N∩C: "
          f"{presentations} finite minimal-strong presentations, "
          f"{len(codes)} distinct full pointed codes, {pairs} raw-host "
          f"pairs, {mutual} mutual pairs ({distinct_mutual} distinct), "
          f"{same_coordinate} same-coordinate distinct pairs, "
          f"{graph_checks} exact J/graph checks")


if __name__ == "__main__":
    main()
