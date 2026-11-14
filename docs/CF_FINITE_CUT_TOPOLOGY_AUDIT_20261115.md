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

## Exact finite-prefix vertex-domain identity

A second theorem, `birthLevelDomain_increasing_prefix`, holds
**without** the empty-request hypothesis. For strictly increasing
`h:ω→ω` and any `m`, it proves the equality of literal vertex sets

    U[h[[0,m)]] = U[h[ω]] ∩ {v : birth(v) ∈ h[[0,m)]}.

The forward inclusion uses inclusion of level sets and the fact
that every vertex's own birth level lies in its complete support.
The reverse uses two distinct facts: each support level lies at
or before the vertex's own birth, and strict increase of `h`
reflects the index order. If `birth(v)=h(k)` with `k<m`,
every level of the support which lies in `range(h)` is
`h(j)` for some `j≤k<m`. Thus its *whole* support lies in
the selected first `m` image levels.

**Independent counterexample challenges:** A non-strict `h`
would not support the index-order reflection; dropping complete
support membership `birth(v)∈σ(v)` would invalidate the forward
direction; and replacing the full supported domain `U[h[ω]]`
by all vertices born at represented levels would invalidate
the reverse direction. The proof uses exactly the stronger
hypotheses established for the actual birth carrier.

Combining this vertex-domain identity with the separately
submitted stage-image theorem in Track E PR #549 will identify
the finite image of the first `m` actual birth stages with the
literal domain `U[h[[0,m)]]`. Until both independent Lean
checks finish, this final combination is an integration
obligation and is not yet presented as a verified corollary.

## Exhaustive finite adversarial regression

The independent script `scripts/check_cf_finite_cut_topology.py`
tests two vertices per level for four levels. A distinguished
vertex at each level has singleton support; the other has
every possible support containing its birth and no later level.
All 64 combined assignments, all pairs of level subsets,
all five finite cuts, all three-step increasing images and
their four prefixes give **82,944** checked equivalences.
This finite regression passed in a local Python execution.
The submitted script repeats it in CI.

Three toy counterexamples demonstrate that the hypotheses
must not be dropped:

- Without a singleton-support detector at level 1, supports
  `{0}` and `{0,1}` cannot distinguish selected sets `∅`
  and `{1}`, so finite-cut reflection fails.
- If a vertex born at level 0 is allowed to have support
  `{0,1}`, agreement on the first level cannot ensure
  agreement on that vertex; support bounded by birth is essential.
- If the image list starts `2,0,3` instead of increasing,
  a vertex born at 2 with support `{0,2}` belongs to the
  full supported domain and is born at the first selected image
  level, but does not belong to the first-level supported prefix.

These are regressions for logical scope, not substitutes
for Lean compilation or for the concrete infinite structure.

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
