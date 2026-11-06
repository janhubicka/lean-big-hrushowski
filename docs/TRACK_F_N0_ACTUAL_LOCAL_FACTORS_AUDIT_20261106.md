# Track F — induced local factors: adversarial referee audit (6 November 2026)

Source: The-big-Hrushovski Section 8a, definitions of (C_B,P_B,g_A(B)). Target branch: Track F #270.

**Exact scope.** For each SCC of a finite two-orientation, the module restricts the entire directed adjacency relation to the *one-component successor closure* (C_B), then takes the pointwise stabilizer of the actual lower part (P_B). It proves successor-closedness of (P_B) inside that induced structure; the resulting code fibre is counted by that induced stabilizer. It also proves the factor does not depend on a vertex chosen to represent (B). Finally it instantiates the already-verified finite data-product lemma with choice sets of cardinality (g_A(B)).

This is a **finite type/data count only**. The function (B\mapsto g_A(B)) is now interpreted in the correct induced orientation; however a bijection between `actualFiniteComponentData` and the permitted linear orders of the *entire finite graph* is not yet proved, nor are recurrence, degree-one Ramsey or the infinite big Ramsey degree.

## Adversarial referee panel (internal independent checks)

1. **Induced-vs-global referee.** An incoming leaf attached to one point of a directed 3-cycle makes the whole orientation rigid, but the component's local stabilizer still has order 3. The code must use (\operatorname{Aut}(A[C_B])_{(P_B)}), never (\operatorname{Aut}(A)_{(P_B)}).
2. **Closure referee.** If (u\in P_B) had an arrow into (B), reachability from (B) to (u) and back would put (u) in (B). The proof explicitly uses this contradiction; it makes no acyclicity assumption.
3. **Pointwise referee.** Swapping the two sinks in a fork fixes their lower set only setwise. The local automorphism definition fixes each old vertex, and the existing negative regression rejects the swap.
4. **Representative referee.** The factor must not change when replacing a chosen generator (x\in B); the proof rewrites both (C_B) and (P_B), including their dependent subtype carriers.
5. **Counting referee.** The final product theorem counts **rankings and independent numeric choice data**, not all permitted vertex orders. The still-missing global bijection is expressly excluded.
6. **Certification referee.** New statements receive no verified marker until the branch's Lean build, standard axiom/placeholder audit and negative finite regressions all pass. This is not external human review.

Finite regressions inherited from Track F exhaust all oriented graphs of order at most five and the local canonical-code fibre sizes. The local factor proofs must compile without `sorry`, `axiom` or unverified imported assumptions.

## Independent concrete counterexample regression

The additional script `scripts/check_track_f_actual_local_factor_examples.py` checks all 653 orientations on at most four vertices, all of their SCC generators, and successor-closedness of the strict lower part. The incoming-leaf directed triangle has **three** local automorphisms of its cycle closure but only **one** automorphism of the whole graph. The fork has pointwise lower-part stabilizer **one** but setwise stabilizer **two**. The regression rejects both incorrect substitutions. It is independent of the Lean implementation and of the product-formula scripts.
