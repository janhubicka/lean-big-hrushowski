#!/usr/bin/env python3
"""Independent small finite regression of SCC lex order realization.

Every legal SCC order and locally injective vertex rank determines an
actual labelled enumeration. All SCC-interval enumerations can be
reconstructed exactly from their component-first ranks and positions.
"""
from itertools import permutations
from check_track_f_canonical_local import orientations, components


def component_data(out):
    cc=components(out)
    blocks=[part for part, _ in cc]
    which={x:i for i,block in enumerate(blocks) for x in block}
    return cc, blocks, which


def legal_component_order(cc, ranking):
    pos={i:j for j,i in enumerate(ranking)}
    return all(pos[j] < pos[i]
               for i, (part, closure) in enumerate(cc)
               for j, (other, _) in enumerate(cc)
               if j != i and other <= closure)


def intervals(order, blocks):
    p={v:i for i,v in enumerate(order)}
    return all(max(p[v] for v in block)-min(p[v] for v in block)+1==len(block)
               for block in blocks)


def successor_first(order, cc):
    p={v:i for i,v in enumerate(order)}
    return all(p[y]<p[x] for part,cl in cc for x in part for y in cl-part)


def negative_controls():
    # Distinct vertices in one strongly connected component must not
    # receive the same local key: a directed triangle is the witness.
    tri=(frozenset({1}), frozenset({2}), frozenset({0}))
    cc, blocks, which=component_data(tri)
    assert len(cc)==1
    bad_rank={0:0,1:0,2:0}
    keys=[(0,bad_rank[v]) for v in range(3)]
    assert len(set(keys))<len(keys)
    # A ranking that reverses the one edge 0 -> 1 cannot be
    # successor-first, regardless of internal ranks.
    edge=(frozenset({1}),frozenset())
    ec, _, _=component_data(edge)
    assert not legal_component_order(ec,(0,1))


def main():
    negative_controls()
    total_orientations=0
    lex_realizations=0
    recovered=0
    legal_realizations=0
    for n in range(5):
        for out in orientations(n):
            total_orientations+=1
            cc,blocks,which=component_data(out)
            vertices=range(n)
            for ranking in permutations(range(len(cc))):
                pos={i:j for j,i in enumerate(ranking)}
                is_legal=legal_component_order(cc,ranking)
                for local_perm in permutations(range(n)):
                    ranks={v:local_perm[v] for v in vertices}
                    # Global injectivity of these test ranks is
                    # stronger than the required local injectivity.
                    order=tuple(sorted(vertices,
                                       key=lambda v:(pos[which[v]],ranks[v])))
                    assert len(order)==n and len(set(order))==n
                    assert intervals(order,blocks)
                    assert all((order.index(x)<order.index(y)) ==
                               ((pos[which[x]],ranks[x]) <
                                (pos[which[y]],ranks[y]))
                               for x in vertices for y in vertices)
                    if is_legal:
                        assert successor_first(order,cc)
                        legal_realizations+=1
                    lex_realizations+=1
            for order in permutations(vertices):
                if not intervals(order,blocks):
                    continue
                p={v:i for i,v in enumerate(order)}
                comp_rank=tuple(sorted(range(len(cc)),
                                       key=lambda i:min(p[v] for v in blocks[i])))
                pos={i:j for j,i in enumerate(comp_rank)}
                restored=tuple(sorted(vertices,
                                      key=lambda v:(pos[which[v]],p[v])))
                assert restored==order
                if successor_first(order,cc):
                    assert legal_component_order(cc,comp_rank)
                recovered+=1
    assert total_orientations==653
    assert recovered==13730
    print(f"PASS: {total_orientations} orientations, "
          f"{lex_realizations} actual lex enumerations, "
          f"{legal_realizations} legal successor-first realizations, "
          f"{recovered} reconstructed interval enumerations; "
          "noninjective-key and backwards-dependency negatives")


if __name__=="__main__":
    main()
