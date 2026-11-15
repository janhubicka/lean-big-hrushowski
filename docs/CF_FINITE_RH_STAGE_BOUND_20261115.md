# Track B — actual finite-stage bounds for (R,H) level lifting

15 November 2026. This fills a specific gap between the certified
finite prescribed-level lifting theorem and the proof of the finite
Ramsey property in Section 3b of *The Big Hrushovski*.

## Statements

Let s be a **finite substructure in the actual ordered partial
(R,H) language**, and let `level : ℕ → ℕ` be strictly increasing
only on the finitely represented birth levels of s.

If every represented source birth level is assigned a target level
less than N, then there is **exactly one** finite (R,H)-embedding
with those prescribed target levels whose entire literal image is
inside (U_N). The map preserves and reflects edges and nonedges,
the level preorder and the canonical linear order, exact R-values,
all defined H-values, and the partial domain of H.

Conversely, for any admissible finite level embedding, literal
image containment in (U_N) is equivalent to the represented
target levels all being below N.

The proof is deliberately elementary once the earlier finite
lifting theorem has been verified: the equivalence
`mem_stageImage_iff_birth_lt` states that a birth-labelled
vertex belongs to (U_N) exactly when its birth level is less
than N. No second finite induction or total old-stage map
is needed.

## Six internal adversarial referee roles

1. **Stage-membership referee.** Both directions use the exact
   identity `v ∈ stageImage F K N ↔ v.1 < N` for the actual
   birth-labelled carrier. No ad hoc isomorphism to another
   finite graph or finite-stage lift is substituted.
2. **Partial-function referee.** The existence theorem
   retains `FiniteRHLevelEmbedding`, whose conditions include
   complete R-values, all defined H-values and reflection of
   H's domain. Merely having image in a stage is not enough
   to imply those properties.
3. **Target-level referee.** The bound is imposed only on
   `representedLevels F K s`. At unrepresented levels
   the level assignment may be arbitrary. This is essential
   for first represented source level 1 mapping to target 0.
4. **Boundary referee.** Empty s and N = 0 are handled
   without special cases. A nonempty map cannot have all
   target levels less than 0, so no false witness is produced.
5. **Uniqueness referee.** The existence-and-uniqueness
   result is derived from the *already certified* exact
   finite (R,H) unique-lifting theorem; adding the
   stage-containment property neither makes a stronger
   uniqueness assumption nor requires an extension of a
   map on an entire old source stage.
6. **Scope/refactoring referee.** These lemmas certify
   the literal containment assertion used in the finite
   Ramsey upper bound. They do NOT prove the finite
   Ramsey colouring argument itself, the countable
   embedding monoid, or an Ellentuck theorem. The three
   new declarations have exact `#print axioms` gates
   and require the full Lean build, placeholder scan
   and finite regressions.

These are independent mathematical **challenge roles**
within an internal adversarial audit, not reports from
six external human referees.

## CI gates

```sh
lake build BigHrushovski.CFFiniteRHStageBound
lake env lean CheckAxiomsCFTrackBRHStageBound.lean
python3 scripts/check_no_placeholders.py
```

The dedicated main-source verification marker may be inserted
beside the phrase asserting that (U_N) contains all
prescribed finite lifts on level sets in ([N]^a) and
([N]^b) **only after exact-head CI succeeds**.
The Ramsey colouring reduction itself remains a separate
proof obligation.
