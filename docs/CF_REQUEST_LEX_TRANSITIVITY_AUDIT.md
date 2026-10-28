# Adversarial audit: transitivity of finite request lex comparison
28 October 2026

The finite C_F request comparator first compares the increasing
old-support tuples. If equal, it compares fresh sizes, and if
those are equal, it compares complete adjacency matrices. Each
coordinate is linearly ordered (Lists have their usual lex order).

The proof of transitivity is a simple case split: the first
unequal support tuple dominates any later coordinates; if all
supports agree, fresh sizes dominate; if all sizes agree, the
adjacency bits compare transitively.

Hostile mathematical checks:

1. A proper prefix of one support tuple precedes the longer
   tuple, matching the original proof of unique level lifting.
2. No code injectivity is needed for transitivity; equality of
   all keys may still occur for distinct request records until
   the next injectivity theorem is proved.
3. A larger fresh size only matters if the complete named
   support tuples are equal.
4. Adjacency matrix comparison only matters if support and
   size are both identical.
5. List equality and Nat equality are transitive, so the
   proof handles chains with equal intermediate coordinates.
6. If both source comparisons are strict in different
   coordinates, the earliest strict coordinate dominates.
7. This theorem does not assign an order on arbitrary countable
   birth vertices or solve the recursive old-order coherence.
8. The current C_F manuscript marker must remain PARTIAL until
   the exact lex comparator is proved total and transported to
   the coherent countable tower.
9. An arbitrary request-rank order is not substituted for the
   exact support/adjacency comparison.
10. An exact axiom declaration and full CI build are required
    before promoting this finite lemma to GREEN.

All roles are internal mathematical adversarial checks.
