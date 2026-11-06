# Track A adversarial validation: finite C0 functional amalgamation

Date: 1 November 2026. Baseline: `main` at `1f5fcd06`.
This is a **role-separated internal referee panel**, not independent
human or agent referees.

## Certified new endpoints (subject to passing CI on this branch)

**1. One-block two-sided functional amalgamation.**
`C0TaggedFunctionalOneBlock.taggedOneBlock_twoSidedFunctionalAmalgam`
works on the *literal* tagged graph `freeGraph G H`. Its input is a
left finite minimal-component presentation; a right graph with one
minimal strong extension over the named common base; shared complete
named base unary values; a frontloaded right common base; and the
standard graph sparsity/agreement hypotheses.

It concludes:
- two-sparsity of the tagged free graph;
- a minimal strong step from the entire old left domain to the joined graph;
- full inducedness of both factor graph embeddings (including nonedges);
- exact image equality for **every vertex** in both complete set-valued
  canonical unary functions, on both factors simultaneously.

`namedBase_strong_of_minimalPresentation` removes a possible circular
premise: from the left minimal-component stages and the fact that
the named values on the common base stay inside that base, it derives
`P ≤ G` using the already formalized finite closed-subset theorem.
No agreement of chronological base orders is assumed.

**2. Literal joined stage identities.**
`C0TaggedStageCuts.joinedIndex_oldStage_left` and
`joinedIndex_oldStage_right` establish the exact finite-set
equalities
`oldStage(joinedIndex,k) = leftTag[oldStage(κL,k)]` for `k≤n`, and
`oldStage(joinedIndex,n+j) = leftDomain ∪ rightTag[oldStage(κR,j)]`
for **all** `j`. Thus the first phase is unchanged and the right
phase has exactly the intended vertices. Empty ranks are permitted.
These theorems have no predimension hypotheses because none are needed.

### Adversarial panel

1. **Referee on premise circularity:** `P≤G` is proved from the original
   left presentation and complete named base values. It is not inferred
   from, or assumed about, the desired amalgam.

2. **Referee on full functions:** preservation means equality of the
   *entire finite vertex-valued images*, not merely agreement on old
   neighbours, component indices, or forward inclusion. The actual
   tagged graph is used; no surrogate free union is assumed equivalent.

3. **Referee on order alignment:** the left component order stays fixed.
   The base orders on the two factors may disagree on incomparable
   components; shared values force only the edge orientations needed.

4. **Referee on no-cross/minimality:** the output minimal-step theorem
   applies to **one** right-hand increment. It must not be promoted
   to a theorem about all concatenated right components before the
   individual joined-stage steps are checked.

5. **Referee on empty/unused levels:** the stage theorem assumes no
   index surjectivity; it covers an empty base, empty left or right
   tails, and gaps in both index codomains. The independent test
   covers 44 carrier shapes, 711,712 indexed assignments and 7,980,984
   exact stage equalities without discrepancy.

6. **Referee on remaining countable bridge:** the end-to-end finite
   functional age theorem and the graph-reduct identification of its
   countable Fraïssé limit are **not** consequences of the new theorem
   without further work. In particular, the existing strong-generic
   uniqueness theorem has hypotheses that must be checked for the
   *actual* functional reduct.

7. **Referee on scope of the right witness:** `hMinimalH` is a graph
   minimal step over the whole named base. It does not force an arbitrary
   `κR` to index the entire right tail as one component. Thus the
   new one-block theorem does **not** assert that
   `joinedIndex κL κR` is a complete valid multi-step witness.
   A separate right-prefix induction is required.

## Next exact Lean target

`taggedJoin_minimalSteps`: under minimal-component stage hypotheses
for both factors, frontloaded right base and common named complete
unary values, every step of `joinedIndex κL κR` is either empty or
minimal strong. Use `joinedIndex_oldStage_left/right` to identify
the literal sets, then split a right stage into a base-only (empty
joined increment) or a tail stage. For the latter, the entire right
base precedes it, no new right vertex is adjacent to the left tail,
and `minimalStrongStep_enlarged_of_local` transports the right
minimality. Avoid restating the full value-transport proof.

Only after combining this with the existing two-sided complete
unary-value theorem should `prop:C0-free-generic` be promoted from
partial. The separate countable reduct construction must still prove
finite strong covers and the labelled strong extension property.

## Tests and status

- The workflow builds the whole Lean umbrella and checks all registered
  declarations against only `propext`, `Classical.choice`,
  `Quot.sound` (plus no-placeholder scan).
- `check_c0_explicit_amalgam.py` already checks 8,459 compatible
  closed-base diagrams, including a non-singleton right component
  with a differently ordered left-interleaved common base.
- `check_c0_joined_stage_cuts.py` independently checks the new exact
  stage identities, including arbitrary non-surjective indexes.
- Do not mark the entire finite amalgamation theorem GREEN until
  the joined-stage minimality theorem and its complete hypotheses pass
  exact axiom and regression audits.
