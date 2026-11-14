# Track E — finite-cut comparison for the natural copy-domain topology

15 November 2026. Independent module, based on `main` (no dependency
on the stacked R/H-copy or RamseySpace-library PRs).

## Statement

Write `V` for the **actual** countable birth-labelled `C_F` carrier.
For a vertex `v`, let `σ(v)` be the set of birth levels occurring
in its **entire finite b-generated closure**. For `S ⊆ ω`, let

    U[S] = {v ∈ V : σ(v) ⊆ S}.

Let `V_<m` be the literal finite birth stage. Suppose every birth
level has an actual empty-old-support birth request. The new Lean
theorem `birthLevelDomain_agree_on_stage_iff` states, for arbitrary
`S,T ⊆ ω` and every `m`,

    S ∩ [0,m) = T ∩ [0,m)
      iff
    U[S] ∩ V_<m = U[T] ∩ V_<m.

This is an equivalence of *membership observations*, not just
inclusion or an abstract isomorphism.

## Proof and consequence

**Forward.** Each vertex born before `m` has its entire generated
closure inside that finite birth stage. Its support is therefore
contained in `[0,m)`. Agreement of the level coordinates makes
membership in the two supported domains identical.

**Reverse.** For each `n<m`, choose a genuine birth vertex `z_n`
from an empty-old-support request at level `n`. The full generated
closure of `z_n` is its whole fresh birth block, so
`σ(z_n)={n}` even when that block has multiple vertices. Hence
`z_n ∈ U[S]` exactly when `n∈S`. Agreement on `V_<m` detects
the membership of each such level.

As the finite birth stages are cofinal among all finite vertex
observations, and finite initial level intervals are cofinal
among finite level-coordinate observations, this establishes
the equality of the corresponding **product subspace topologies**
on supported level sets and their vertex-domain images.
The remaining comparison with the `RamseySpace` approximation
metric is the standard fact that, on infinite level sets,
finite initial segments of the strictly increasing enumeration
generate the same topology as finite membership observations.
The current Lean module formalizes the precise finite-cut
equivalence, *not* that final topological-space equality.

## Adversarial referee panel (internal independent challenges)

1. **Correct source.** The statement uses the original literal
   vertex carrier, its actual `stageImage`, and the actual
   complete b-generated support — no copied surrogate.
2. **Wrong support avoided.** Replacing `σ(v)` by just the birth
   level of `v` would make the forward observation invalid for
   complete functional closures. The proof calls the verified
   `birthLevelDomain_local_birth` theorem.
3. **Reverse is genuinely two-sided.** The reverse does not follow
   from monotonicity or closedness of `U[S]`. It explicitly picks
   a singleton-level detector.
4. **No block-size fallacy.** The detector's *level* support is
   singleton although its fresh block may have many vertices.
5. **No hidden surjectivity.** No selected increasing map, lifting
   or functional embedding is assumed: `S,T` are arbitrary sets.
6. **Empty stages and gaps.** The result includes `m=0`, empty
   selected level sets, and arbitrarily large gaps in `S,T`.
7. **Honest hypotheses.** The converse needs an actual detector
   for each level. We assume the proved empty-support request
   condition rather than treating inhabited stages as automatic.
8. **Topology scope.** The equivalence concerns product
   observations. It does not by itself prove the paper's A.1–A.4
   Ramsey-space axioms or identify a topology on embeddings
   rather than on their ranges.
9. **Trust and compilation.** The new theorem has an exact
   `#print axioms` endpoint and a dedicated CI workflow.
   Until that exact-head workflow succeeds, this proof is a
   submitted candidate, **not** a kernel-verified theorem.

## Integration order

- Compile and axiom-audit this independent finite-cut theorem.
- Check the staged PRs for actual ordered R/H copy domains,
  finite first-image-level approximations and the pinned
  `SupportedEllentuck` instance on their *current* heads.
- Bridge the increasing-enumeration approximation metric with
  finite membership observations and then state the natural
  copy-domain topology equality in Lean.
- Update the Section 6 validation marker only after both
  topologies and the exact functional copy range are checked.
  The `R_0` and rational `R_F` clauses remain separate.

These are internal mathematical adversarial checks, not reviews
by external human referees.
