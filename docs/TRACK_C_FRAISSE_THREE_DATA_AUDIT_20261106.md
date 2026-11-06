# Track C — remove redundant empty-base condition from the generic criterion

The published strong Fraisse limit M_F is built from a class C_F
whose finite members all have strictly d-closed empty base.
Consequently the global empty-base property on a countable
comparison generic is not an independent fourth assumption
once its full finite induced growth membership is known.

The new `HasFiniteFraisseData F G` records precisely:
(i) membership of all finite induced subgraphs in C_F;
(ii) finite globally strictly d-closed covers; and
(iii) complete induced finite d-closed responses fixing every
prescribed old value and reflecting all nonedges.

The theorem `toStrictGenericity` invokes **only** the independently
verified finite-to-global empty-base transfer from PR #346.
`PresentedFraisseData` adds a genuine vertex equivalence
`ℕ ≃ V` for an arbitrary countably infinite carrier, not
an assumed graph isomorphism. Its conversion to the four-part
genericity interface is fieldwise.

The final real-birth theorem reuses the previously kernel-checked
arbitrary-carrier recognition from PR #350, without repeating the
countable back-and-forth construction. This streamlines the
manuscript's final M_F identification.

## Internal adversarial panel

**Class referee:** the finite empty-base property is explicitly
required and does not follow from F(0)=0. The reduction holds
for every finite induced C_F subgraph, not just finite stages.

**Strong embedding referee:** the response field is a complete
strict d-closed induced extension property; no stronger hidden
homogeneity property or weaker homomorphism substitutes for it.

**Carrier referee:** an actual equivalence from ℕ to V ensures
the comparison structure is countably infinite; mere Countable V
would allow V to be finite and is not enough.

**Non-circularity referee:** neither of the three input fields
nor the enumeration includes an isomorphism from the birth
graph. The conclusion is obtained only after applying verified
finite-to-countable uniqueness.

**Re-use referee:** the new declarations are short wrappers
around #344, #346 and #350, avoiding parallel copies of their
back-and-forth and finite-subtype arguments.

**Certification referee:** the entire new source requires its
own isolated Lean build and explicit `#print axioms` endpoint
checks. Paper lemma verification status must not be promoted
before the singleton request is derived and the actual named
M_F comparison is instantiated.

Status at submission: CI pending. Internal role-separated
checking does not constitute external human referee approval.
