#!/usr/bin/env python3
"""Adversarial classification of raw C0 closure-components by FULL code keys.

For unrelated actual finite minimal-strong presentations, checks the
equivalence of equality of complete unpointed (support, E, C) codes,
mutual C-membership and equality of complete raw C-values.

Crucial negative control: a path and a triangle can have identical
support, pointed root and complete C-incidence matrix but DIFFERENT
adjacency matrices. Such codes must represent different components.
"""
from check_c0_raw_host_full_relabel import sample, closed
from check_c0_mutual_code_key_J import key
from check_c0_raw_host_graph import make_code
from check_c0_coordinate_host_finite import finite_component_values


def main():
    pool, presentations = sample()
    codes = tuple(pool)
    values = {q:closed(q) for q in codes}
    pairs = key_equal = distinct_key_equal = same_support_C = 0
    for q in codes:
        for r in codes:
            pairs += 1
            eqkey = key(q) == key(r)
            mutual = r in values[q] and q in values[r]
            eqvalue = values[q] == values[r]
            assert eqkey == mutual == eqvalue
            if eqkey:
                key_equal += 1
                if q != r:
                    distinct_key_equal += 1
            if (q[0],q[3]) == (r[0],r[3]) and q[2]!=r[2]:
                same_support_C += 1

    assert presentations == 1401
    assert distinct_key_equal > 0
    # Actual three-vertex chronological minimal-strong presentations,
    # both with C(0)={0}, C(1)={0,1}, C(2)={0,1,2}.
    edges_path={(0,1),(1,2)}
    edges_triangle={(0,1),(1,2),(0,2)}
    kappa=(0,1,2)
    C1=finite_component_values(kappa,edges_path)
    C2=finite_component_values(kappa,edges_triangle)
    assert C1==C2
    labels={0:2,1:5,2:9}
    q_path=make_code(edges_path,C1,C1[2],2,labels)
    q_tri=make_code(edges_triangle,C2,C2[2],2,labels)
    assert q_path[0]==q_tri[0] and q_path[1]==q_tri[1]
    assert q_path[3]==q_tri[3] and q_path[2]!=q_tri[2]
    assert key(q_path)!=key(q_tri)
    print(f"PASS full raw C0 component keys: {presentations} finite "
          f"minimal-strong presentations, {len(codes)} complete code "
          f"vertices, {pairs} ordered pairs, {key_equal} equal-key "
          f"pairs ({distinct_key_equal} distinct), {same_support_C} "
          "same-support/C negative pairs, path/triangle counterexample")


if __name__ == "__main__":
    main()
