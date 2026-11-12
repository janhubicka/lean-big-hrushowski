#!/usr/bin/env python3
"""Independent finite test of the exact canonical-order data bijection.

The identity between actual canonical enumerations and SCC ranking
plus component-order data is checked exhaustively. The product formula
is separately checked numerically: it is NOT yet the Lean theorem.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components, stabilizer_card
from check_track_f_global_canonical_count import legal_components, legal_local_codes


def run(out):
    n = len(out)
    comps = components(out)
    blocks = [part for part,_ in comps]
    locals_ = [tuple(permutations(sorted(b))) for b in blocks]
    g_prod = 1
    for b,c in comps:
        g_prod *= stabilizer_card(out,c,c-b)
    canonical_data_orders = set()
    legal_rankings = 0
    rank_count_total = 0
    for rank in permutations(range(len(blocks))):
        positions = {i:j for j,i in enumerate(rank)}
        legal = all(positions[j]<positions[i]
                    for i,(b,c) in enumerate(comps)
                    for j,(other,_) in enumerate(comps)
                    if j!=i and other <= c)
        if not legal:
            continue
        legal_rankings += 1
        rank_orders = set()
        for chosen in product(*locals_):
            order = tuple(x for i in rank for x in chosen[i])
            assert len(order)==n and len(set(order))==n
            assert legal_components(order,comps)
            assert order not in rank_orders
            if legal_local_codes(out,order,comps):
                rank_orders.add(order)
                assert order not in canonical_data_orders
                canonical_data_orders.add(order)
        assert len(rank_orders)==g_prod, (out,rank,len(rank_orders),g_prod)
        rank_count_total += len(rank_orders)
    actual_canonical = {
        order for order in permutations(range(n))
        if legal_components(order,comps) and
           legal_local_codes(out,order,comps)
    }
    assert canonical_data_orders == actual_canonical
    assert len(actual_canonical)==rank_count_total==legal_rankings*g_prod
    return len(actual_canonical),legal_rankings


def negative_controls():
    # A triangle has six labelled internal orders but only three
    # lexicographically canonical choices.
    tri=(frozenset({1}),frozenset({2}),frozenset({0}))
    assert len(list(permutations(range(3))))==6
    a,b=run(tri)
    assert a==3 and b==1
    # Interleaving components is forbidden by the actual interval rule.
    tri_iso=tri+(frozenset(),)
    assert not legal_components((0,3,1,2),components(tri_iso))


def main():
    negative_controls()
    structs=actual=rankings=0
    for n in range(5):
        for o in orientations(n):
            c,r=run(o)
            structs+=1
            actual+=c
            rankings+=r
    assert structs==653 and actual==1764, (structs, actual)
    print(f"PASS: {structs} orientations, {actual} canonical labelled orders, "
          f"{rankings} legal rankings; data/image bijection, "
          "fibre-sum identity, finite product, and interval negative tests")


if __name__=="__main__":
    main()
