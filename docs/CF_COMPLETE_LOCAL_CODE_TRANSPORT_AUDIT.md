# Adversarial audit: complete ordered local C_F code transport

29 October 2026

## Claim under review

For two actual finite-stage request records r and t, an increasing
isomorphism of their literal old-support subtypes and an increasing
isomorphism of their fresh ordinal intervals transport the complete
local coordinate list exactly. If the induced graph relation agrees
on every pair of these coordinates, the full ordered adjacency
matrices are identical.

The old-support order isomorphism can be constructed from a map
strictly increasing only on the selected old source S, provided the
target support is exactly the literal image of the source support.

## Role-separated hostile reviews

1. **Order and coordinate referee.** The old and fresh lists are
   independently sorted before concatenation. The proof must
   preserve the concatenation boundary, handle empty supports,
   and use an *order isomorphism* (not merely an injection) on each
   complete finite carrier. A proper increasing injection of
   finite sets of unequal sizes does not map the complete
   coordinate list onto the target list.

2. **Graph-code referee.** The matrix comparison is not a
   comparison of old-neighbour sets, degrees, or positive edges
   only. It requires induced adjacency equivalence on the entire
   local graph: old-old, old-fresh and fresh-fresh pairs,
   including reflection of all nonedges. The generic
   orderedAdjacencyBits_of_coordinate_eq theorem then applies
   without repeating graph arguments.

3. **Partial-embedding referee.** The finite lift supplies an
   order-preserving map only on a selected b-closed old source,
   not on the entire stage. The constructed support order
   isomorphism therefore uses only strict monotonicity on S and
   the literal support image equality. The target level may
   be earlier than the source level.

4. **Lean and statement referee.** Exact declaration names
   are recorded in CheckAxioms.lean. The full build, axiom
   audit, placeholder scan and finite regressions must pass
   on the same commit before the results are marked verified.
   The proof does not use sorry, admit, or new axioms.

5. **Amalgamation referee.** This result does not construct a
   target request, establish the growth-class predicate or
   uniform size bound, prove the global induced map of a
   simultaneous block batch, or complete finite unique
   level lifting. In particular, a single-block response
   cannot be iterated if all blocks must occupy the same
   prescribed target level.

## Additional manuscript check

The source A_<i and its image are b-closed, which in this
specific C_F tower implies strict d-closedness by
birthBlockClosed_global_dClosed. This is a nontrivial
prerequisite for transporting each local support; mere
b-closedness of an arbitrary unrelated structure would not
imply it. The manuscript should cite the finite closure
lemma at this step rather than treating b-closedness alone
as sufficient.

These are distinct adversarial mathematical checks conducted
within the project, not claims of independent external
human referees.
