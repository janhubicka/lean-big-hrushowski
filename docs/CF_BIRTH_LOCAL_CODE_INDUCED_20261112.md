# Track B: complete literal request code in the birth graph — adversarial audit

12 November 2026. Four exact proposed kernel endpoints.

The source code of each \(\mathcal C_F\) request describes a graph on
the literal old support and all fresh ordinals. The finite level
construction embeds this graph inducedly; the canonical map into
the countable birth graph also preserves and reflects adjacency.
Composition gives the equality for the **whole** local graph
and the three old–old, old–fresh and fresh–fresh specializations.

## Six independent adversarial roles

1. **Source and target names.** The map is exactly
   `toVertex F K (n+1) ∘ localTag ... r`. The old vertex
   identity is `toVertex_old`; a fresh vertex is literally
   `⟨n,⟨r,i⟩⟩`. No arbitrary local isomorphism is substituted.

2. **No missing nonedges.** The proof relies on two *iff*
   theorems, `levelGraph_local_adj_iff` and
   `countableGraph_stage_induced`, not one-sided edge
   preservation. The conclusion reflects all absent edges.

3. **Every local coordinate.** The principal theorem quantifies
   over all `Sum (SupportCarrier U r.support) (Fin ...)`
   pairs. The three displayed consequences are not a substitute
   for that general theorem. They verify each of the three
   kinds of matrix entries explicitly.

4. **Finite stage coherence.** The theorem uses exactly
   `stage F K (n+1)`, whose graph is definitionally the
   simultaneous tagged graph over `stage F K n`. It does
   not use the graph of a different finite stage or a
   separately chosen request catalogue.

5. **Class and free-join scope.** The underlying construction
   and the induced graph theorem are unconditional in `F,K`.
   This makes no new assertion that every finite stage lies
   in the published growth class; that is a separate theorem
   with its own class hypotheses.

6. **Remaining uniqueness gap.** This is a *reading* theorem,
   not equality of the request codes of two arbitrary
   embeddings. To derive code equality, first establish a
   matching ordered coordinate map on old support and full
   target block using support/block-image rigidity and the
   finite ordinal lemma. Then apply inducedness to all
   pairs and use `request_eq_of_support_size_adjacency`.
   Finally induct over represented levels, not all stages.

## Mechanical check

```sh
lake build BigHrushovski.CFBirthLocalCodeInduced
lake env lean CheckAxiomsCFTrackBLocalCodeInduced.lean
python3 scripts/check_no_placeholders.py
```

Do not merge or promote manuscript validation markers until
exact-head CI, standard-axiom checks and placeholder scans
succeed. These six internal review roles are not independent
external referees.
