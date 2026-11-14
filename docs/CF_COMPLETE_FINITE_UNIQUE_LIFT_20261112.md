# Track B: complete finite unique level lifting — adversarial audit

12 November 2026. This candidate integrates the already verified
finite prescribed-lift existence theorem with the *arbitrary-map*
uniqueness induction under review in PRs #479, #481 and #485.
No external green validation marker is justified before the
entire stack passes exact-head Lean CI and ordinary axiom auditing.

## Precise result

Let s be any finite b-closed source in the actual countable
birth-labelled C_F structure. Let h assign target birth levels
with strict increase **only on the levels represented in s**.
There exists exactly one injective induced finite map f:s→M_F^†
which respects h, the birth-level preorder and canonical order,
and the complete b-functional structure.

There likewise exists exactly one such map in the manuscript's
genuine R/H language: R-values are exactly transported; every
defined H-value is exactly transported; and the partial domain
of H is preserved and reflected. The SAME concrete lift from
the already verified existence construction witnesses the
R/H conditions.

## Six independent adversarial referee roles

1. **Existence and uniqueness refer to the same language.**
   The b theorem calls the finite existence result whose
   witness simultaneously satisfies ALL graph/b/level/order
   conditions. The uniqueness induction compares any other
   witness with that exact map. There is no choice of a
   different existence witness mid-proof.
2. **Actual R/H operations and partiality.** The RH theorem
   takes its existence witness directly from
   `finiteSourcePrescribedLift`, whose exact R-values,
   all defined H-values and domain reflection were proved
   in PR #416. The R/H uniqueness theorem invokes the
   previously verified closed-source equivalence with
   complete b-values. At no point is H silently totalized.
3. **No strengthened level hypothesis.** Only the predicate
   `StrictOnRepresented F K s h` occurs. No globally
   strictly increasing map of all ℕ is required.
   Empty s, source/target gaps and first represented
   source level mapping to target zero remain covered.
4. **Arbitrary-map uniqueness.** The uniqueness induction
   in #481 uses exact support images, full complete ordered
   adjacency codes including nonedges, literal target tag
   equality and exact fresh ordinal values. It does not
   assume the other embedding is the canonical recursion.
   Both embeddings need only maps of the selected finite
   source, not whole finite old stages.
5. **Formal proof integrity.** The exact construction
   `finiteSourcePrescribedLift` and its proven graph,
   b, level, order and R/H properties are explicitly
   assembled in the RH witness. The two ExistsUnique
   theorems use kernel-checked functional extensionality,
   not an unverified assertion of uniqueness.
6. **Scope of the paper.** These are the finite lifting
   existence-and-uniqueness endpoints. Compatibility
   under restriction and composition still requires
   explicit verification that the restrictions/composites
   are actual embeddings in the correct language, and
   then an application of uniqueness. The countable
   embedding monoid and ensuing Ramsey results remain
   separate. Do not mark those as validated on this
   PR alone, even if all finite endpoints pass.

Six roles are internal adversarial checks, not independent
outside referees.

## Mechanical verification

```sh
lake build BigHrushovski.CFCompleteFiniteUniqueLevelLift
lake env lean CheckAxiomsCFTrackBCompleteFiniteUniqueLift.lean
python3 scripts/check_no_placeholders.py
```
