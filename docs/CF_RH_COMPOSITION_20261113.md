# Track B: actual finite R,H composition

13 November 2026. Stacked on canonical finite composition PR #515,
itself stacked on arbitrary partial composition PR #509.

## Claim

Let s be a finite b-closed source, e its prescribed finite
level1 lift, and g the prescribed finite level2 lift of the
literal finite image e[s]. The target level assignment on s is
level2∘level1. The preceding canonical composition theorem
constructs the required represented-level strictness proof and
proves g∘e literally equals the canonical lift for this assignment.

The new theorem additionally proves that the **same composite**
preserves exact complete R-values, all H-values when H is
defined, and reflects the domain of the genuinely partial H
operation. Its proof uses equality of functions and the existing
certified `finiteSourcePrescribedLift_RHValues`, not a second
reimplementation of the recursive construction.

## Internal six-role adversarial review

1. **Language accuracy:** The transfer is about actual complete
   R(v) and partial H(S). It includes H-domain reflection, not only
   transport of defined H-values or an auxiliary b-value.
2. **Partial maps:** The second lift has source *exactly* the
   finite image of the first. The extension by identity outside
   s used to state R,H values is NOT claimed to be an embedding
   outside s, nor to preserve all infinite structure values.
3. **Source closure:** Finite b-closure of s and the complete
   b-closure of the intermediate image are explicitly needed.
   The intermediate closure is available from #515, not
   inferred from graph adjacency alone.
4. **Levels:** Strictness of the composite assignment is
   derived from the composite embedding and imposed only at
   levels represented in s. Empty sources, skipped levels,
   and target level zero remain allowed.
5. **Rigidity:** Equality with the canonical lift comes from
   the previously verified *arbitrary finite embedding*
   uniqueness theorem, not an assumption that recursive choices
   are themselves unique.
6. **Scope and dependencies:** The corollary is a finite
   manuscript-language statement. It is not the countable
   unique-lift theorem or monoid isomorphism, and does not
   identify the rational-level embedding space. Do not promote
   those manuscript validation markers.

These are internal adversarial tests, not claims of six human
referee reports.

## Validation

```sh
lake build BigHrushovski.CFPrescribedFiniteRHComposition
lake env lean CheckAxiomsCFTrackBRHComposition.lean
python3 scripts/check_no_placeholders.py
```

The stack must pass exact-head Lean, standard axiom and placeholder
audits before merge or manuscript marker promotion.
