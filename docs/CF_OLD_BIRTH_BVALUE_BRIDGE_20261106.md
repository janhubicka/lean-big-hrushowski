# Track B adversarial review: complete old birth-b-value reconstruction

6 November 2026. Role-separated internal mathematical audit,
not independent external human referee reports.

## Exact lemmas

A finite b-closed source s has a genuine stage-n selected old
carrier S=stageCut s n.  The entire actual birth b-value of
each selected old source vertex lies in S, because both s and
the entire stage-image U_n are b-closed.

The finite value `cutOldBirthBValue` is the *literal preimage*
of the entire countable birth-b-value under the canonical
stage-n inclusion, restricted to S. The exact image theorem
proves it contains every member of the value, including the
whole old support and whole fresh block.

For any target old-stage vertex w∈U_m,
`stageOldBirthBValue m w` is the corresponding literal
full-stage preimage. Its image under the canonical birth map
is exactly the true value `birthBValue(toVertex m w)`.

For any old map e:S→U_m (defined only on S), exact preservation
of the finite old value
`(cutOldBirthBValue u).image e = stageOldBirthBValue(e u)`
is *equivalent* to exact preservation of the full countable
birth-b-value after the target birth map. This is the precise
hypothesis used by the previously verified all-vertex
one-level functional lemma.

## Adversarial referee roles

1. **Closure referee:** `birthBValue_subset_of_closed`
   is applied separately to the finite source s and to
   `stageImage n`. It is NOT inferred from graph inducedness.
   Both are b-closed for already verified reasons.
2. **Source-domain referee:** the old selected value is
   restricted to the literal subtype S, not the whole
   original stage U_n. There is no total map U_n→U_m.
3. **Full-value referee:** the finite preimage includes the
   *whole* birth support and every fresh ordinal, not
   merely neighbour vertices or an arbitrary generating set.
4. **Injectivity referee:** recovery of equality between
   finite target subsets uses the kernel-verified injectivity
   of the target birth map `toVertex m`. The images
   cannot be equated just from a noninjective map.
5. **Empty cases referee:** if s or U_m is empty, all
   declarations remain well typed; the old map from empty S
   imposes vacuous per-vertex conditions. No dummy vertex.
6. **Chronology referee:** complete b-values for vertices
   born before stage n remain within stage n, regardless
   of how many source levels are unrepresented.
7. **Sufficiency referee:** this theorem identifies and
   transfers the old-value INDUCTION HYPOTHESIS. It does
   NOT prove such preservation is automatic for arbitrary
   induced embeddings; the induction must construct it.
8. **Independence referee:** the source/target birth-value
   results rely on existing b-closure and stage maps,
   not on the finite level-lifting lemma being proved.
   There is no circular use of genericity/monoid claims.
9. **Kernel referee:** exactly three endpoints are listed
   in `CheckAxiomsCFTrackBOldBirth.lean`, collected by
   merged PR #310. Full Lean build, standard-axiom scan,
   no-placeholder check and all regressions must pass.
10. **Manuscript referee:** no theorem is promoted to a
    green marker until exact integrated CI passes. The
    complete finite unique lifting and monoid remain partial.

## Next step

Transport both the old-value preimage and the new-block
birth-b-value lemma through the canonical
`selectedCutEquiv` to produce a one-level theorem on
the ACTUAL birth-labelled finite cut. Then induct over
represented levels, inserting target ascents as needed
and proving uniqueness by complete request code recovery.
