# Track B adversarial audit — literal fresh birth b-values

6 November 2026. Internal role-separated mathematical reviewers,
not independent external human reports.

## Precise claim

For a selected fresh vertex `(n,r,i)`, its complete countable
birth-labelled auxiliary value is **exactly** the image of the
selected-carrier value consisting of its literal old support
and the whole fresh request block:

    birthBValue(n,r,i) =
      image (toVertex(n+1) ∘ selectedSourceMap)
        (selectedBlockBValue(r)).

If `e:S→U_m` is a genuinely partial increasing old-stage map
with an admissible actual target request for each selected block,
the corresponding target birth vertex has auxiliary value

    birthBValue(m,transport(r),i) =
      image (toVertex(m+1) ∘ selectedGrowthBatchMapSubtype)
        (selectedBlockBValue(r)).

Both sets are literal FINITE SETS of vertices of the countable
birth carrier; no abstract isomorphism or under-specified inclusion.

## Adversarial roles and objections

1. **Whole-value referee:** the source includes *every* fresh
   ordinal in the block and the entire named old support,
   not merely its fresh neighbours. Both inclusions are proved
   via the exact set-image equality from the selected batch.
2. **Partial old-source referee:** the target map acts only on
   the subtype S. No total map U_n→U_m is constructed; the
   formula includes the empty target old stage when S=∅.
3. **Literal-label referee:** the birth map `toVertex` is
   the actual canonical map on the finite-stage carrier,
   preserving request tags/ordinals. No copy or renumbering.
4. **Graph/reflection referee:** positive edges and nonedges
   enter via the separately verified constructed request;
   this lemma itself is a functional-value identity, not an
   independent proof of graph inducedness.
5. **Old-values referee:** the theorem asserts equality for
   fresh vertices only; it does NOT silently infer the old
   vertex case from inducedness. The old value equality remains
   an induction hypothesis in the verified all-vertex
   `selectedGrowthBatchMapSubtype_allBValues` theorem.
6. **Stage-gap referee:** the current target vertex is born
   at stage m. Moving its representative into a later target
   stage does not change the birth vertex or its complete
   `birthBValue`; this is the separate ascent interface
   under PR #320 (CI not yet passed).
7. **Uniqueness referee:** even exact complete b-value transport
   of the constructed map does NOT prove an arbitrary
   `(R,H)`-embedding is uniquely determined by assigned levels.
   Recover full target request codes and finite ordinals first.
8. **Kernel referee:** all three exact endpoints are in
   independent `CheckAxiomsCFTrackBBirth.lean`, included by the
   glob-based CI merged in PR #310; no `sorry`, private axioms,
   missing imports, or unverified green manuscript marker
   is allowed.
9. **Manuscript referee:** no text or marker is changed in the
   mathematical paper by this PR. Only after full CI may
   a separate local green citation for the fresh-value bridge
   be added.

## Remaining principal bridge

Use the source-cut equivalence to express each ACTUAL birth
b-value of an *old* source vertex in the selected subtype,
then combine the old-value induction hypothesis with the
verified one-level all-vertex map. Assemble the finite
represented-level induction (including skipped source
levels and arbitrary target gaps). The full uniqueness,
restriction/comp and embedding monoid remain unproved.
