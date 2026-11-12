#!/usr/bin/env python3
"""Independent finite component-order gluing and inverse decomposition.

Checks literal equality of all internal SCC comparisons and the exact
global component interval order, without quotienting by isomorphism.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components


def legal_component_order(cc, ranking):
    p = {i: j for j, i in enumerate(ranking)}
    return all(p[j] < p[i]
               for i, (part, closure) in enumerate(cc)
               for j, (other, _) in enumerate(cc)
               if i != j and other <= closure)


def is_successor_first(order, cc):
    p = {x: i for i, x in enumerate(order)}
    return all(p[y] < p[x] for part, closure in cc
               for x in part for y in closure - part)


def is_intervals(order, cc):
    p = {x: i for i, x in enumerate(order)}
    return all(max(p[x] for x in part) - min(p[x] for x in part) + 1 == len(part)
               for part, _ in cc)


def main():
    total_structures, total_glued, total_legal, total_interval = 0, 0, 0, 0
    for n in range(5):
        for out in orientations(n):
            total_structures += 1
            cc = components(out)
            blocks = [part for part, _ in cc]
            all_local = [list(permutations(sorted(part))) for part in blocks]
            glued_orders = set()
            for ranking in permutations(range(len(blocks))):
                legal = legal_component_order(cc, ranking)
                for choices in product(*all_local):
                    glued = tuple(v for i in ranking for v in choices[i])
                    assert len(glued) == n and set(glued) == set(range(n))
                    assert is_intervals(glued, cc)
                    p = {v: j for j, v in enumerate(glued)}
                    # Complete comparisons are recovered within each SCC.
                    for B, order in zip(blocks, choices):
                        assert all((p[x] < p[y]) == (order.index(x) < order.index(y))
                                   for x in B for y in B)
                    assert glued not in glued_orders
                    glued_orders.add(glued)
                    total_glued += 1
                    if legal:
                        assert is_successor_first(glued, cc)
                        total_legal += 1
            for order in permutations(range(n)):
                if is_intervals(order, cc):
                    # Recover the ranking and each local order; concatenation
                    # must give the exact original labelled enumeration.
                    p = {v: i for i, v in enumerate(order)}
                    ranking = tuple(sorted(range(len(blocks)),
                                           key=lambda i: min(p[v] for v in blocks[i])))
                    choices = [tuple(x for x in order if x in part)
                               for part in blocks]
                    assert tuple(v for i in ranking for v in choices[i]) == order
                    assert order in glued_orders
                    total_interval += 1

    assert total_structures == 653, total_structures
    assert total_glued == total_interval == 13730, (total_glued,total_interval)
    print(f"PASS: {total_structures} orientations; {total_glued} glued labelled "
          f"orders = {total_interval} all SCC-interval orders; "
          f"{total_legal} legal successor-first assemblies. "
          "Exact inverse reconstruction and collision controls.")


if __name__ == "__main__":
    main()
