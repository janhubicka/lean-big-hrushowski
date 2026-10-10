"""Exhaustive independent test of gap-free stage labelling.

An arbitrary injection A -> B and arbitrary bijection A -> Fin(card A)
are extended using a disjoint tail. Exhaustively check numeric preservation,
injectivity, and image exactly the initial segment of size card B.

This diagnostic does not replace the Lean proof.
"""
from itertools import permutations

checked = 0
for old_size in range(6):
    for new_size in range(old_size, 7):
        for injected_image in permutations(range(new_size), old_size):
            inverse = {vertex: a for a, vertex in enumerate(injected_image)}
            tail = [vertex for vertex in range(new_size) if vertex not in inverse]
            tail_rank = {vertex: idx for idx, vertex in enumerate(tail)}
            for old_labels in permutations(range(old_size)):
                labels = {
                    vertex: (
                        old_labels[inverse[vertex]]
                        if vertex in inverse
                        else old_size + tail_rank[vertex]
                    )
                    for vertex in range(new_size)
                }
                assert set(labels.values()) == set(range(new_size))
                assert len(set(labels.values())) == new_size
                assert all(
                    labels[injected_image[a]] == old_labels[a]
                    for a in range(old_size)
                )
                assert all(labels[vertex] >= old_size for vertex in tail)
                checked += 1

print(f"Checked {checked:,} finite gap-free labelling diagrams.")
