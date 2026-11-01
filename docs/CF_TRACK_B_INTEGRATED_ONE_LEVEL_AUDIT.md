# Track B: integrated partial-source one-level audit

1 November 2026

## Integration scope

This integration branch starts from current `main` after PR #263
(full inducedness of actual partial-source batches). It brings in
source-level results from PR #264 (complete new-block b-values), PR #265
(sorted literal support transport) and PR #267 (exact full request lex
transport); a new `CFActualSubtypeStageOrder` module identifies the
literal comparison with the **inherited finite-stage order** for source
stage `n+1` and target stage `m+1` even when `m<n`.

The exact API is `e : SupportCarrier (stage F K n).carrier S →
(stage F K m).carrier`. The source old stage need not embed in the
target old stage. The new stage-order result assumes the existing
selected-growth transport conditions for every selected request;
that record includes literal support inclusion, induced old support
and d-closedness in the entire target old stage.

## Adversarial referee roles

1. **Domain referee:** `S=∅`, target old stage empty and source old
   stage nonempty remains admissible. There is no auxiliary total
   old-stage function and no use of `Nonempty` target.
2. **Closure referee:** old image must be strictly d-closed in the
   entire target old stage. The local support conditions alone do
   not force this. A full one-level embedding must carry this premise.
3. **Graph referee:** complete inducedness is a separate merged theorem
   (#263), including all reflected nonedges between old and fresh
   vertices and between different fresh blocks.
4. **Lex referee:** the tuple order compares literal supports first;
   equal supports compare fresh sizes and full ordered adjacency
   matrices; identical requests compare fresh ordinal values.
   The new partial request comparison is not a replacement by an
   arbitrary `Fintype.equivFin` ranking.
5. **Representation referee:** the generic tagged comparison is
   identified with the *actual* recursive `stageLinearOrder`
   on both levels using `taggedLexLt_stage_iff`, not only with
   an abstract `TaggedLexLt` relation.
6. **Functional referee:** the transported new-block b-value
   includes the whole old literal support and *all* fresh vertices.
   Values at previously embedded old vertices must be preserved by
   the future represented-level induction.
7. **Uniqueness referee:** one-level inducedness/order/value
   preservation does not prove uniqueness of a finite lift.
   Still required: rigidity of request tags under an arbitrary
   embedding, positions within each complete block, induction over
   represented levels, restriction and composition.
8. **Kernel referee:** exact axiom endpoints were added to
   `CheckAxioms.lean`. No green manuscript marker for the new
   stage-order theorem until the integration head passes the full
   GitHub Actions workflow, including build, axiom, placeholders,
   and finite regression tests.

## Status and proposed manuscript shortening

Pending integrated CI. All statements above concern the one-level
partial selected batch, not the full finite unique lifting theorem
or the monoid isomorphism.

Once verified, a single one-level lemma can replace the
manuscript's interleaved total-map references. Its hypotheses must
explicitly include induced increasing old-subtype embedding,
old-image strict d-closedness, complete b-values of the old vertices,
and support closure/admissibility for all selected requests.
Existence for an arbitrary finite functional source then follows by
induction over its represented levels. Uniqueness and functorial
compatibility require their own proof, after which the countable
self-embedding monoid may be deduced.

These are role-separated internal checks, not independent human
referee reports.
