# Adversarial audit — actual first roots of tagged CF blocks

19 October 2026

## Statement
Each actual fresh request r at birth level n determines a finite old support P_r, a complete finite fresh block B_r, and its distinguished first ordinal zero. The minimal strict d-closed step P_r <_d P_r∪B_r in the finite tagged level is carried by the *literal induced birth map* into the countable graph. The complete induced relation (including nonedges) is required to transport minimality. Each old support vertex has birth level < n.

For every finite set closed under the auxiliary b-operation, replacing each of its vertices by the first ordinal of its birth block produces a finite set of **existing** vertices in that closed set.

## Hostile reviews

1. **Nonempty increment:** `r.code.2.fresh_pos` is derived from the minimal strict d-closed step; no root ordinal is assumed for a zero-sized block.
2. **Actual tag:** Different requests remain disjoint even if isomorphic over a support; the root is the ordinal zero *with the same tag and birth level*.
3. **No quotient:** The map `toVertex F K (n+1)` is the existing coherent birth map; no new direct limit or relabelling.
4. **Inducedness:** Use `countableGraph_stage_induced` as an iff, not a forward homomorphism, for the complete local graph.
5. **Minimality:** Transport `taggedLocal_minimal` using `minimalDClosedStep_image_iff`, not merely the old/new-neighbour bound.
6. **Earlier support:** Every literal old support vertex came from stage n, so its birth index is strictly below n. This is exactly the induction measure for root recovery.
7. **Closure consistency:** A b-closed set containing any vertex in a tagged block contains ordinal zero, so the set `rootsOf s` is a subset of s.
8. **Remaining gap:** This module *does not* prove `H(R(v))=C(v)` or preservation of H-value domains; the induction that uses these certificates is a separate next theorem.

These are internal role-separated adversarial checks, not independent external human referees. Promote a result only after exact Lean build, axiom output and placeholder checks pass.
